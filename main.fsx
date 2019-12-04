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
type Token = {tag : Tag; pos : Position}
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

type Disjoins = Set<Tag * Tag>
type MMExpr = 
| ExprFloating of Label * Symbol * Symbol
| ExprEssential of Label * Symbol * Symbol [] * Disjoins * hyps : MMExpr []
| ExprAxiom of Label * Symbol * Symbol [] * Disjoins * hyps : MMExpr []
| ExprProof of Label * Symbol * Symbol [] * Disjoins * hyps : MMExpr [] * proof : MMExpr []

type State = {
    // Local
    vars_active : Set<Tag>
    vars_floating : Set<Tag>
    statements_floating : Label list
    statements_essential : Label list
    disjoint : Set<Tag * Tag>
    }

type SemanticError =
| DuplicateVar of Symbol
| DuplicateCon of Symbol
| FloatingStatementVarInactive of Symbol
| FloatingStatementVarAlreadyFloating of Symbol
| DuplicateLabel of Label * Label
| LabelNotFound of Label
| DuplicateDisjoint of Symbol * Symbol
| SymbolInactive of Symbol

exception SemanticException of SemanticError

let ord' a b = if a < b then a,b else b,a
let ord (a : Symbol) (b : Symbol) = ord' a.tag b.tag
let disjoins_fold f s l =
    let rec loop1 i s =
        let rec loop2 j s = if j < l then loop2 (j+1) (f i j s) else loop1 (i+1) s
        if i < l then loop2 (i+1) s else s
    loop1 0 s

let semantic prove (x : MMToken []) = 
    let er x = raise (SemanticException x)
    let global_statements = Dictionary(HashIdentity.Structural)
    let active_constants = HashSet(HashIdentity.Structural)
    let disjoint_try_ord (a : Symbol) (b : Symbol) = if a.tag = b.tag then er (DuplicateDisjoint(a, b)) else ord a b
    let label = function ExprFloating(x,_,_) | ExprEssential(x,_,_,_,_) | ExprAxiom(x,_,_,_,_) | ExprProof(x,_,_,_,_,_) -> x
    let global_try_add t =
        let x = label t
        match global_statements.TryGetValue x.tag with
        | true, t' -> er (DuplicateLabel(x,label t'))
        | false, _ -> global_statements.Add(x.tag,t)
    let global_try_get x =
        match global_statements.TryGetValue x.tag with
        | true, t' -> t'
        | false, _ -> er (LabelNotFound x)

    let mandatory (s : State) (v : Symbol []) = 
        let free_vars =
            let free_vars = HashSet(HashIdentity.Structural)
            v |> Array.iter (fun x ->
                if Set.contains x.tag s.vars_active then free_vars.Add(x.tag) |> ignore
                elif active_constants.Contains x.tag then ()
                else er (SymbolInactive x)
                )
            Seq.toArray free_vars
        let disjoins_free_vars_filtered = 
            disjoins_fold (fun i j d -> 
                let ab = ord' free_vars.[i] free_vars.[j]
                if Set.contains ab s.disjoint then Set.add ab d else d
                ) Set.empty free_vars.Length
        let hyps =
            let rec loop = function
                | f :: fs, e :: es -> if f.tag < e.tag then f :: loop (fs, e :: es) else e :: loop (f :: fs, es)
                | [], l | l, [] -> l
            loop (List.rev s.statements_floating, List.rev s.statements_essential)
            |> List.toArray |> Array.map global_try_get
        disjoins_free_vars_filtered, hyps

    let rec loop s (x : MMToken []) =
        Array.fold (fun (s : State) x ->
            match x with
            | TokVars v -> 
                let f (s : Set<Tag>) (x : Symbol) = if Set.contains x.tag s then er (DuplicateVar x) else Set.add x.tag s
                { s with vars_active = Array.fold f s.vars_active v}
            | TokCons c ->
                Array.iter (fun (x : Symbol) -> if active_constants.Add x.tag then er (DuplicateCon x) else ()) c
                s
            | TokDisjoint d ->
                { s with disjoint = disjoins_fold (fun i j s -> Set.add (disjoint_try_ord d.[i] d.[j]) s) s.disjoint 0 }
            | TokFloating(l,c,v) ->
                global_try_add (ExprFloating(l,c,v))
                if Set.contains v.tag s.vars_active then
                    if Set.contains v.tag s.vars_floating = false then 
                        {s with vars_floating=Set.add v.tag s.vars_floating; statements_floating=l :: s.statements_floating}
                    else er (FloatingStatementVarAlreadyFloating v)
                else er (FloatingStatementVarInactive v)
            | TokEssential(l,c,v) ->
                let disjoints, hyps = mandatory s v
                global_try_add (ExprEssential(l,c,v,disjoints,hyps))
                {s with statements_essential=l :: s.statements_essential}
            | TokAxiom(l,c,v) ->
                let disjoints, hyps = mandatory s v
                global_try_add (ExprAxiom(l,c,v,disjoints,hyps))
                s
            | TokProof(l,c,v,p) ->
                let disjoints, hyps = mandatory s v
                let p = Array.map global_try_get p
                global_try_add (ExprProof(l,c,v,disjoints,hyps,p))
                prove (l,c,v,s.disjoint,hyps,p)
                s
            | TokInclude l -> loop s l
            | TokBlock l -> loop s l |> ignore; s 
            ) s x
    loop {vars_active=Set.empty; vars_floating=Set.empty; statements_floating=[]; statements_essential=[]; disjoint=Set.empty} x |> ignore
