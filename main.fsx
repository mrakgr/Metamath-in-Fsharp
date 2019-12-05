open System

#if INTERACTIVE
#r @"packages\FParsec.1.1.0-RC\lib\net45\FParsecCS.dll"
#r @"packages\FParsec.1.1.0-RC\lib\net45\FParsec.dll"
#endif
open System.Collections.Generic
open FParsec

/// Types

type Tag = int
type Tokenizer() =
    let tag_to_string = ResizeArray<string>()
    let string_to_tag = Dictionary<string,Tag>(HashIdentity.Structural)

    member _.Tag x = 
        match string_to_tag.TryGetValue x with
        | true, c -> c
        | false, _ ->
            let c = tag_to_string.Count
            tag_to_string.Add x
            string_to_tag.Add(x,c)
            c

    member _.String (c : Tag) = tag_to_string.[c]
    member _.Count = tag_to_string.Count

type Position = int64
type [<CustomEquality;CustomComparison>] Token = 
    {tag : Tag; pos : Position}

    override a.Equals(b) = 
        match b with
        | :? Token as b -> a.tag = b.tag
        | _ -> false

    override a.GetHashCode() = a.tag

    interface IComparable with
        member a.CompareTo(b) = 
            match b with
            | :? Token as b -> compare a.tag b.tag
            | _ -> raise <| ArgumentException "Invalid comparison for Token."

type Label = Token
type Symbol = Token

// Tokenization

type MMToken =
| TokVars of Symbol []
| TokCons of Symbol [] 
| TokDisjoint of Symbol []
| TokFloating of Label * Symbol * Symbol
| TokEssential of Label * Symbol * Symbol []
| TokAxiom of Label * Symbol * Symbol []
| TokProof of Label * Symbol * Symbol [] * Label []
| TokBlock of MMToken []
| TokInclude of MMToken []

type ParserState = { symbols : Tokenizer; labels : Tokenizer }

let many_array_first_elem x0 = let ra = ResizeArray<_>() in ra.Add(x0); ra
let many_array_fold_state (ra : ResizeArray<_>) x = ra.Add(x); ra
let many_array_result_from_state (ra : ResizeArray<_>) = ra.ToArray()
let many_array p =
    Inline.Many(elementParser = p, stateFromFirstElement = many_array_first_elem, foldState = many_array_fold_state,
                resultFromState = many_array_result_from_state, resultForEmptySequence = (fun () -> [||]))
let many1_array p =
    Inline.Many(elementParser = p, stateFromFirstElement = many_array_first_elem, foldState = many_array_fold_state,
                resultFromState = many_array_result_from_state)
let many2_array p = many_array p >>= fun x s -> if x.Length >= 2 then Reply x else Reply(Error,messageError "The number of elements parsed must be at least two.")

let is_label c = isAsciiLetter c || isDigit c || c = '-' || c = '_' || c = '.'
let is_math_symbol c = '!' <= c && c <= '~' && c <> '$'

let comment =
    let rec body s = (charsTillString "$" true System.Int32.MaxValue >>. (skipChar ')' <|> (skipChar '(' >>. fail "Nested comments are not allowed.") <|> body)) s
    skipMany (skipString "$(" >>. body >>. (spaces1 <|> eof))

let spaces1 = spaces1 >>. comment
let spaces = spaces >>. comment
let skip_string x = skipString x >>. (spaces1 <|> eof)

let label' = many1SatisfyL is_label "Ascii letter, digit, `-`, `_` or `.`"
let label = label' >>= (fun x s -> Reply({tag = s.UserState.labels.Tag x; pos = s.Index})) .>> spaces1
let math_symbol = 
    many1SatisfyL is_math_symbol "Ascii character between `!` and `~` (excluding `$`.)" 
    >>= (fun x s -> Reply({tag = s.UserState.symbols.Tag x; pos = s.Index})) .>> spaces1

let between a b c = between (skip_string a) (skip_string b) c

let rec tokenize is_outer s =
    choice [
        between "$v" "$." (many_array math_symbol |>> TokVars)
        between "$c" "$." (fun s -> 
            if is_outer then (many_array math_symbol |>> TokCons) s 
            else Reply(Error, messageError "The constant statement is allowed only in the outermost scope.")
            )
        between "$d" "$." (many2_array math_symbol |>> TokDisjoint)
        between "${" "$}" (many_array (tokenize false) |>> TokBlock)
        between "$[" "$]" ((label' >>= fun path s ->
            if is_outer then
                match runParserOnFile many_tokenize s.UserState path System.Text.Encoding.Default with
                | Success(x,_,_) -> Reply(TokInclude x)
                | Failure(_,er,_) -> Reply(Error,er.Messages)
            else
                Reply(Error, messageError "The file include statement is allowed only in the outermost scope.")
            ) .>> spaces1)
        label >>= fun label' ->
            choice [
                between "$f" "$." (pipe2 math_symbol math_symbol (fun typecode var -> TokFloating(label',typecode,var)))
                between "$a" "$." (pipe2 math_symbol (many1_array math_symbol) (fun typecode sym_seq -> TokAxiom(label',typecode,sym_seq)))
                between "$e" "$." (pipe2 math_symbol (many1_array math_symbol) (fun typecode sym_seq -> TokEssential(label',typecode,sym_seq)))
                between "$p" "$." (pipe3 math_symbol (many1_array math_symbol .>> skip_string "$=") (many1_array label) (fun typecode sym_seq labels -> TokProof(label',typecode,sym_seq,labels)))
                ]
        ] s
and many_tokenize = spaces >>. many_array (tokenize true) .>> eof

type Disjoints = (Tag * Tag) []
type MMExpr = 
| ExprFloating of Label * Symbol * Symbol
| ExprEssential of Label * Symbol * Symbol [] * Disjoints * hyps : MMExpr []
| ExprAxiom of Label * Symbol * Symbol [] * Disjoints * hyps : MMExpr []
| ExprProof of Label * Symbol * Symbol [] * Disjoints * hyps : MMExpr [] * proof : MMExpr []

type State = {
    // Local
    vars_active : Map<Tag,Position> // Symbol
    vars_floating : Map<Tag,Position> // Symbol
    hyps_in_scope : Map<Tag,Position> // Label
    disjoint : Set<Tag * Tag> // Symbol * Symbol
    }

type SemanticError =
| DuplicateVar of Symbol * Symbol
| DuplicateCon of Symbol * Symbol
| FloatingStatementVarInactive of Symbol
| FloatingStatementVarAlreadyFloating of Symbol * Symbol
| DuplicateLabel of Label * Label
| LabelNotFound of Label
| DuplicateDisjoint of Symbol * Symbol
| SymbolInactive of Symbol
| LabelOutOfScope of Label
| NotEnoughArgumentsOnStack of Label
| UnificationErrorLabelHypFloating of ((int * int) * Label) * (Symbol * Symbol) * (Symbol * Symbol [])
| UnificationErrorLabelHypEssential of ((int * int) * Label) * (Symbol * Symbol []) * (Symbol * Symbol [])
| StackNotOne of Stack<Symbol * Symbol []>
| UnficationErrorProof of Label * (Symbol * Symbol []) * (Symbol * Symbol [])
| DisjointNotActiveVar of Symbol
| DisjointVarViolationsLabelHyp of ((int * int) * Label) * ((Tag * Tag) * (Tag * Tag)) []
| DisjointVarViolationsLabel of Label * ((Tag * Tag) * (Tag * Tag)) []

exception SemanticException of SemanticError

let ord a b = if a < b then a,b else b,a
let disjoins_fold f s l =
    let rec loop1 i s =
        let rec loop2 j s = if j < l then loop2 (j+1) (f i j s) else loop1 (i+1) s
        if i < l then loop2 (i+1) s else s
    loop1 0 s

let semantic (x : MMToken []) = 
    let er x = raise (SemanticException x)
    let global_statements = Dictionary(HashIdentity.Structural)
    let active_constants = Dictionary(HashIdentity.Structural)
    let disjoint_assert_ord (a : Symbol) (b : Symbol) = if a = b then er (DuplicateDisjoint(a, b)) else ord a b
    let label = function ExprFloating(x,_,_) | ExprEssential(x,_,_,_,_) | ExprAxiom(x,_,_,_,_) | ExprProof(x,_,_,_,_,_) -> x
    let global_statements_assert_add t =
        let x = label t
        match global_statements.TryGetValue x.tag with
        | true, t' -> er (DuplicateLabel(x,label t'))
        | false, _ -> global_statements.Add(x.tag,t)
    let global_statements_assert_get x =
        match global_statements.TryGetValue x.tag with
        | true, t' -> t'
        | false, _ -> er (LabelNotFound x)

    let mandatory (s : State) (v : Symbol []) = 
        let free_vars' = 
            let free_vars = HashSet(HashIdentity.Structural)
            v |> Array.iter (fun x ->
                if Map.containsKey x.tag s.vars_active then free_vars.Add(x.tag) |> ignore
                elif active_constants.ContainsKey x.tag then ()
                else er (SymbolInactive x)
                )
            free_vars
        let free_vars = Seq.toArray free_vars'
        let disjoints_given_free_vars = 
            let disjoints_given_free_vars = ResizeArray()
            disjoins_fold (fun i j () -> 
                let ab = ord free_vars.[i] free_vars.[j]
                if Set.contains ab s.disjoint then disjoints_given_free_vars.Add ab
                ) () free_vars.Length
            disjoints_given_free_vars.ToArray()
        let hyps = 
            Map.toArray s.hyps_in_scope 
            |> Array.choose (fun (tag,pos) -> 
                match global_statements_assert_get {tag=tag; pos=pos} with
                | ExprFloating(_,_,v) as r -> if free_vars'.Contains v.tag then Some r else None
                | ExprEssential _ as r -> Some r
                | _ -> failwith "impossible"
                )
        disjoints_given_free_vars, hyps
        
    let rec loop s (x : MMToken []) =
        Array.fold (fun (s : State) x ->
            match x with
            | TokVars v -> 
                let f (s : Map<Tag,Position>) (x : Symbol) = 
                    match Map.tryFind x.tag s with
                    | Some pos -> er (DuplicateVar({tag=x.tag; pos=pos}, x))
                    | None -> Map.add x.tag x.pos s
                { s with vars_active = Array.fold f s.vars_active v}
            | TokCons c ->
                Array.iter (fun (x : Symbol) -> 
                    match active_constants.TryGetValue x.tag with
                    | false, _ -> active_constants.Add(x.tag,x.pos)
                    | true, pos -> er (DuplicateCon({tag=x.tag; pos=pos}, x))
                    ) c
                s
            | TokDisjoint d ->
                Array.iter (fun a -> if Map.containsKey a.tag s.vars_active = false then er (DisjointNotActiveVar a)) d
                { s with 
                    disjoint = 
                        disjoins_fold (fun i j s' -> 
                            let a,b = disjoint_assert_ord d.[i] d.[j]
                            Set.add (a.tag,b.tag) s'
                            ) s.disjoint 0 }
            | TokFloating(l,c,v) ->
                global_statements_assert_add (ExprFloating(l,c,v))
                if Map.containsKey v.tag s.vars_active then
                    match Map.tryFind v.tag s.vars_floating with
                    | None -> {s with vars_floating=Map.add v.tag v.pos s.vars_floating; hyps_in_scope=Map.add l.tag l.pos s.hyps_in_scope}
                    | Some pos -> er (FloatingStatementVarAlreadyFloating({tag=v.tag; pos=pos}, v))
                else er (FloatingStatementVarInactive v)
            | TokEssential(l,c,v) ->
                let disjoints, hyps = mandatory s v
                global_statements_assert_add (ExprEssential(l,c,v,disjoints,hyps))
                {s with hyps_in_scope=Map.add l.tag l.pos s.hyps_in_scope}
            | TokAxiom(l,c,v) ->
                let disjoints, hyps = mandatory s v
                global_statements_assert_add (ExprAxiom(l,c,v,disjoints,hyps))
                s
            | TokInclude l -> loop s l
            | TokBlock l -> loop s l |> ignore; s 
            | TokProof(l,c,v,proof_label) ->
                let proof_expr =
                    let disjoint, hyps = mandatory s v
                    let p = 
                        proof_label |> Array.map (fun x ->
                            match global_statements_assert_get x with
                            | ExprAxiom _ | ExprProof _ as r -> r
                            | ExprFloating _ | ExprEssential _ as r -> if Map.containsKey x.tag s.hyps_in_scope then r else er (LabelOutOfScope x)
                            )
                    global_statements_assert_add (ExprProof(l,c,v,disjoint,hyps,p))
                    p
                let _ =
                    let stack = Stack()
                    (proof_label, proof_expr) ||> Array.iter2 (fun l -> function
                        | ExprFloating(_,c,v) -> stack.Push(c,[|v|])
                        | ExprEssential(_,c,v,_,_) -> stack.Push(c,v)
                        | ExprAxiom(_,c,v,d,hyps) | ExprProof(_,c,v,d,hyps,_) ->
                            if stack.Count < hyps.Length then er (NotEnoughArgumentsOnStack l)

                            let assert_disjoints (d : Disjoints) (m : Map<Tag, Symbol []>) on_fail =
                                let m = Map.map (fun _ -> Array.choose (fun x -> if active_constants.ContainsKey x.tag = false then Some x.tag else None) >> Array.distinct) m
                                let errors = Stack()
                                d |> Array.iter (fun (a,b) ->
                                    Array.iter (fun a' ->
                                        Array.iter (fun b' ->
                                            if a' = b' || Set.contains (ord a' b') s.disjoint = false then errors.Push((a,b),(a',b'))
                                            ) m.[b]
                                        ) m.[a]
                                    )
                                if errors.Count > 0 then er (on_fail (errors.ToArray()))

                            let substitute (m : Map<Tag, Symbol []>) (v : Symbol []) =
                                Array.collect (fun x ->
                                    match Map.tryFind x.tag m with
                                    | Some v -> v
                                    | None -> [|x|]
                                    ) v

                            Array.mapFoldBack (fun x () -> (x,stack.Pop()),()) hyps ()
                            |> fst |> Array.fold (fun (m, i) (hyp,(c',v')) ->
                                match hyp with
                                | ExprFloating(_,c,v) -> 
                                    if c = c' then Map.add v.tag v' m
                                    else er (UnificationErrorLabelHypFloating (((i,hyps.Length),l),(c,v),(c',v')))
                                | ExprEssential(_,c,v,d,_) -> 
                                    assert_disjoints d m (fun e -> DisjointVarViolationsLabelHyp(((i,hyps.Length),l), e))
                                    let v = substitute m v
                                    if c = c' && v = v' then m
                                    else er (UnificationErrorLabelHypEssential (((i,hyps.Length),l),(c,v),(c',v')))
                                | _ -> failwith "impossible"
                                |> fun m -> m, i+1
                                ) (Map.empty, 1)
                            |> fun (m,_) -> 
                                assert_disjoints d m (fun e -> DisjointVarViolationsLabel(l, e))
                                stack.Push(c,substitute m v)
                        )

                    if stack.Count = 1 then 
                        let c', v' = stack.Pop()
                        if c = c' && v = v' then ()
                        else er (UnficationErrorProof(l,(c,v),(c',v')))
                    else er (StackNotOne stack)
                s
            ) s x
    loop {vars_active=Map.empty; vars_floating=Map.empty; hyps_in_scope=Map.empty; disjoint=Set.empty} x |> ignore

