open System.Collections.Generic

#if INTERACTIVE
#r @"packages\FParsec.1.1.0-RC\lib\net45\FParsecCS.dll"
#r @"packages\FParsec.1.1.0-RC\lib\net45\FParsec.dll"
#endif
open FParsec

/// Types

type Label = int
type Labels = Set<Label>
type Disjoints = (string * string) []
type Symbol = string
type Symbols = Symbol []

type Statement =
    | Floating of string * string
    | Essential of string * Symbols * Disjoints
    | Axiom of string * Symbols * Disjoints * Statement [] 
    | Proof of string * Symbols * Disjoints * Statement []

/// Parsing

type State = {
    // Local
    disjoints : Map<string,Set<string>>
    vars : Map<string,Label option>
    essentials : Labels // includes the free vars of the essentials
    // Global
    cons : HashSet<string>
    labels : Dictionary<string,Label>
    statements : Dictionary<Label,Statement>
    }

let tag_create (x : State) label = let c = x.labels.Count in x.labels.Add(label, c); c

let many_array_first_elem x0 = let ra = ResizeArray<_>() in ra.Add(x0); ra
let many_array_fold_state (ra : ResizeArray<_>) x = ra.Add(x); ra
let many_array_result_from_state (ra : ResizeArray<_>) = ra.ToArray()
let many1_array p s =
    Inline.Many(elementParser = p, stateFromFirstElement = many_array_first_elem, foldState = many_array_fold_state,
                resultFromState = many_array_result_from_state) s
let many_array p s =
    Inline.Many(elementParser = p, stateFromFirstElement = many_array_first_elem, foldState = many_array_fold_state,
                resultFromState = many_array_result_from_state, resultForEmptySequence = (fun () -> [||])) s

let is_label c = isAsciiLetter c || isDigit c || c = '-' || c = '_' || c = '.'
let is_math_symbol c = '!' <= c && c <= '~' && c <> '$'

let label s = (many1SatisfyL is_label "Ascii letter, digit, `-`, `_` or `.`") s
let math_symbol s = (many1SatisfyL is_math_symbol "Ascii character between `!` and `~` (excluding `$`.)") s

let comment s =
    let rec body s = (charsTillString "$" true System.Int32.MaxValue >>. (skipChar ')' <|> (skipChar '(' >>. fail "Nested comments are not allowed.") <|> body)) s
    (skipMany (skipString "$(" >>. body >>. (spaces1 <|> eof))) s

let spaces1 s = (spaces1 >>. comment) s
let spaces s = (spaces >>. comment) s
let terminal x s = (skipString x >>. (spaces1 <|> eof)) s
let skip_string x s = (skipString x >>. spaces1) s 

let inline er x = Reply(Error, messageError x)
let inline proceed_if_active check x (s : CharStream<_>) = 
    if check x s.UserState then Reply(x)
    else er (sprintf "%s must be active." x)

let var s = 
    (math_symbol >>= fun x s -> 
        let u = s.UserState
        let a = u.vars
        if Map.containsKey x a = false then s.UserState <- {u with vars=Map.add x None a}; Reply(())
        else er (sprintf "Variable %s is already active." x)
        ) s

let con s = 
    (math_symbol >>= fun x s -> 
        let u = s.UserState
        let a = u.cons
        if a.Contains x = false then a.Add x |> ignore; Reply(x)
        else er (sprintf "Constant %s is already active." x)
        ) s

let vars s = (between (skip_string "$v") (terminal "$.") (skipMany (var >>. spaces1))) s
let cons s = (between (skip_string "$c") (terminal "$.") (skipMany (con >>. spaces1))) s

let is_floating_var x u =
    match Map.tryFind x u.vars with
    | Some (Some _) -> true
    | _ -> false

let active_constant s = (math_symbol >>= proceed_if_active (fun x u -> u.cons.Contains x)) s
let active_variable s = (math_symbol >>= proceed_if_active (fun x u -> Map.containsKey x u.vars)) s
let active_math_symbol s = 
    (math_symbol >>= fun x s ->
        let u : State = s.UserState
        if u.cons.Contains x || Map.containsKey x u.vars then Reply(x)
        else er (sprintf "%s is neither a constant nor an active variable." x)
        ) s

let er_label_is_active label = er (sprintf "Label %s is already active." label)
let floating label s = 
    let check_floating var (s : CharStream<_>) =
        if is_floating_var var s.UserState = false then Reply(var)
        else er (sprintf "There may not be two active $f statements containing the same variable %s." var)
    (
    skip_string "$f" >>.
    tuple2 (active_constant .>> spaces1) (active_variable >>= check_floating .>> spaces1 .>> terminal "$.") 
    >>= fun (con, var) -> 
        updateUserState (fun u ->
            let tag = tag_create u label
            u.statements.Add(tag,Floating(con, var))
            {u with vars=Map.add var (Some tag) u.vars}
            )
    ) s

let free_vars (u : State) ar = Array.fold (fun s x -> if u.cons.Contains x then s else Set.add x s) Set.empty ar
let free_vars_label (u : State) x = Set.map (fun x -> u.labels.[x]) x

let disjoints_used (disjoints : Map<_,_>) (free_vars : Set<string>) = 
    let f x next prev s =
        match prev with
        | Some x' when Set.contains x disjoints.[x'] -> next prev ((x', x) :: s)
        | Some _ -> next prev s
        | None -> s
        |> fun s -> if Map.containsKey x disjoints then next (Some x) s else next None s
    Set.foldBack f free_vars (fun prev s -> s) None [] |> List.toArray

let essential label s =
    (
    skip_string "$e" >>.
    tuple2 (active_constant .>> spaces1) (many_array (active_math_symbol .>> spaces1) .>> terminal "$.") 
    >>= fun (c, v) -> updateUserState (fun u -> 
        let tag = tag_create u label
        let free_vars = free_vars u v
        u.statements.Add(tag,Essential(c,v,disjoints_used u.disjoints free_vars))
        {u with essentials=free_vars_label u free_vars + Set.add tag u.essentials}
        )
    ) s

let disjoint s = 
    let check x msg _ = if x then Reply(()) else er msg
    let h = HashSet(HashIdentity.Structural)
    (
    skip_string "$d"
    >>. (skipMany (active_variable >>= (fun x -> check (h.Add(x)) (sprintf "%s cannot be disjoint with itself." x)) >>. spaces1))
    >>= (fun _ -> check (h.Count >= 2) "The $d statement needs at least two variables")
    >>= fun _ -> updateUserState (fun u ->
        {u with disjoints=
                let f x' next x disjoint =
                    match x with
                    | None -> next (Some x') disjoint
                    | Some x as prev ->
                        let add x x' m =
                            match Map.tryFind x m with
                            | Some d -> Map.add x (Set.add x' d) m
                            | None -> Map.add x (Set.singleton x') m
                        disjoint |> add x x' |> add x' x |> next prev |> next (Some x')

                Seq.foldBack f h (fun _ x -> x) None u.disjoints
            }
        )
    >>. terminal "$."
    ) s

let labels_to_statements (u : State) x = Set.toArray x |> Array.map (fun x -> u.statements.[x])
    
let modifyUserState f (s: CharStream<_>) = f s.UserState; Reply(())
let axiom label s = 
    (
    skip_string "$a" >>.
    tuple2 (active_constant .>> spaces1) (many_array (active_math_symbol .>> spaces1))
    >>= fun (c,sym_seq) -> modifyUserState (fun u -> 
        let tag = tag_create u label
        let free_vars = free_vars u sym_seq
        u.statements.Add(tag,Axiom(c,sym_seq,disjoints_used u.disjoints free_vars,labels_to_statements u (free_vars_label u free_vars + u.essentials)))
        )
    >>. terminal "$." 
    ) s

let active_label s = (label >>= proceed_if_active (fun x u -> u.labels.ContainsKey x)) s

let print_body (c, v) = [|[|c|]; v|] |> Array.concat |> String.concat " "
let error_typecode c c' = sprintf "Unification failed. Typecode %s <> %s" c c'
let error_body a b = sprintf "Unification failed. %s <> %s" (print_body a) (print_body b)

let proof label s = 
    
    /// Proving
    let substitute (u : State) (m : Map<string, Symbols>) (desc : Symbols) =
        let subvars = Dictionary(HashIdentity.Structural)
        subvars,
        Array.collect (fun x ->
            match Map.tryFind x m with
            | Some v ->
                match subvars.TryGetValue x with
                | false, _ -> subvars.[x] <- Array.fold (fun s -> function Variable x -> Set.add x s | Constant _ -> s) Set.empty v
                | true, _ -> ()
                v
            | None -> [|x|]
            ) desc

    let disjointness_check (disjoint_vars : Map<string, Set<string>>) (substs_map : Dictionary<string, Set<string>>) =
        [||] // TODO: Fix this tomorrow.
        //let fails = ResizeArray()

        //let check (kv : KeyValuePair<_,_>) next prev = 
        //    let var', subvars' = kv.Key, kv.Value
        //    match prev with
        //    | None -> Option.iter (fun d' -> next (Some (var',subvars',d'))) (Map.tryFind var' disjoint_vars)
        //    | Some (var, subvars, d) ->
        //        if Set.contains var' d then
        //            Set.iter (fun v ->
        //                let v_disjoint_vars = Option.defaultValue Set.empty (Map.tryFind v disjoint_vars)
        //                let violations = subvars' - v_disjoint_vars
        //                Set.iter (fun v' -> fails.Add((var,v),(var',v'))) violations
        //                ) subvars
        //    next prev

        //Seq.foldBack check substs_map (fun _ -> ()) None
        //fails.ToArray()

    let assert_non_disjoint disjoint substituted_vars on_succ on_fail =
        let r = disjointness_check disjoint substituted_vars
        if Array.isEmpty r then on_succ ()
        else 
            Array.map (fun ((var,v),(var',v')) -> 
                if v = v' then sprintf "The variables %s and %s which should be disjoint have %s in common." var var' v
                else sprintf "The variables %s and %s which should be disjoint have %s which does not have disjointness constraints for %s." var var' v v'
                ) r
            |> String.concat "\n" // TODO: Fparsec is eating newlines here.
            |> on_fail

    let prove_mandatory m hyp item on_succ on_fail =
        match hyp, item with
        | Floating(c,v),(c',v') -> if c = c' then on_succ (Map.add v v' m) else on_fail (error_typecode c c')
        | Essential(c,sym_seq,disjoint),(c',sym_seq') -> 
            if c = c' then
                let substituted_vars, sym_seq = substitute m sym_seq
                if sym_seq = sym_seq' then assert_non_disjoint disjoint substituted_vars (fun () -> on_succ m) on_fail
                else on_fail (error_body (c,sym_seq) (c', sym_seq'))
            else on_fail (error_typecode c c')
        | _ -> failwith "impossible"

    (
    skip_string "$p" >>.
    tuple2 (active_constant .>> spaces1) (many_array (active_math_symbol .>> spaces1)) 
    .>> skip_string "$="
    >>= fun (c,sym_seq) ->
        let stack = Stack()
        let prove_label label (s : CharStream<State>) = 
            let u = s.UserState 
            let t = u.labels.[label]
            match u.statements.[t] with
            | Floating(c,v) when Map.containsKey label u.vars -> stack.Push(c,[|Variable v|]); Reply(())
            | Floating(c,v) -> er "The floating statement has to be in scope."
            | Essential(c,v,_) when Set.contains t u.essentials -> stack.Push(c,v); Reply(())
            | Essential(c,v,_) -> er "The essential statement has to be in scope."
            | Proof(con,sym_seq,disjoint,hyps) | Axiom(con,sym_seq,disjoint,hyps) when hyps.Length > stack.Count -> er "Not enough hypotheses on stack."
            | Proof(con,sym_seq,disjoint,hyps) | Axiom(con,sym_seq,disjoint,hyps) ->
                let stack_items = Array.zeroCreate hyps.Length
                let rec pop i = if i > 0 then stack_items.[i-1] <- stack.Pop(); pop (i-1) else ()
                pop hyps.Length
        
                let rec loop i m = 
                    if i < hyps.Length then prove_mandatory m hyps.[i] stack_items.[i] (loop (i+1)) (er << sprintf "(error for item %i out of %i) %s" (i+1) hyps.Length)
                    else 
                        let substituted_vars, sym_seq = substitute m sym_seq
                        assert_non_disjoint disjoint substituted_vars (fun () -> stack.Push(con,sym_seq); Reply(())) er 
                loop 0 Map.empty

        let prove_finish s = 
            if stack.Count = 1 then 
                let (c',sym_seq') = stack.Pop() 
                if (c,sym_seq) = (c',sym_seq') then Reply(()) else er (error_body (c,sym_seq) (c',sym_seq'))
            else 
                Seq.map print_body stack
                |> String.concat "\n"
                |> sprintf "Only one premise must be left on the stack after the labels have been processed. Got:\n%s"
                |> er

        (skipMany (active_label >>= prove_label >>. spaces1) >>. prove_finish)
        >>. modifyUserState (fun u -> 
                let tag = tag_create u label
                let free_vars = free_vars u sym_seq
                u.statements.Add(tag,Proof(c,sym_seq,disjoints_used u.disjoints free_vars,labels_to_statements u (free_vars_label u free_vars + u.essentials)))
                )
    >>. terminal "$."
    ) s

let block next s =
    let f next (s : CharStream<State>) = 
        let u = s.UserState
        let r = next s
        s.UserState <- {s.UserState with vars=u.vars; disjoints=u.disjoints; essentials=u.essentials}
        r
    between (skip_string "${") (terminal "$}") (f (skipMany next)) s

let checked_label s = 
    let proceed_if_inactive_label label (s : CharStream<_>) =
        if s.UserState.labels.ContainsKey label = false then Reply(label)
        else er_label_is_active label
    (label >>= proceed_if_inactive_label) s

let rec parser s =
    let rec inner s = 
        choice [|
            checked_label >>= fun label -> spaces1 >>. choice [|floating label; essential label; axiom label; proof label|]
            vars; disjoint; block inner
            |] s
    
    let outer s = 
        choice [|
            checked_label >>= fun label -> spaces1 >>. choice [|floating label; essential label; axiom label; proof label|]
            vars; disjoint; block inner; cons; file_include
            |] s

    (spaces >>. skipMany outer .>> eof) s

and file_include (s : CharStream<_>) =
    (
    label >>= fun x s ->
        match runParserOnFile parser s.UserState "" System.Text.Encoding.Default with
        | Success(r,u,_) -> s.UserState <- u; Reply(r)
        | Failure(msg,_,_) -> er msg
    ) s

let default_userstate () = 
    {
    disjoints = Map.empty; vars = Map.empty; essentials = Set.empty
    cons = HashSet(HashIdentity.Structural); labels = Dictionary(HashIdentity.Structural); statements = Dictionary(HashIdentity.Structural)
    } 

let verify prog = runParserOnString parser (default_userstate()) "main" prog
let verify_file path = runParserOnFile parser (default_userstate()) path System.Text.Encoding.Default

/// Testing

let demo0 =
    """
$( Declare the constant symbols we will use $)
    $c 0 + = -> ( ) term wff |- $.
$( Declare the metavariables we will use $)
    $v t r s P Q $.
$( Specify properties of the metavariables $)
    tt $f term t $.
    tr $f term r $.
    ts $f term s $.
    wp $f wff P $.
    wq $f wff Q $.
$( Define "term" (part 1) $)
    tze $a term 0 $.
$( Define "term" (part 2) $)
    tpl $a term ( t + r ) $.
$( Define "wff" (part 1) $)
    weq $a wff t = r $.
$( Define "wff" (part 2) $)
    wim $a wff ( P -> Q ) $.
$( State axiom a1 $)
    a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
$( State axiom a2 $)
    a2 $a |- ( t + 0 ) = t $.
    ${
       min $e |- P $.
       maj $e |- ( P -> Q ) $.
$( Define the modus ponens inference rule $)
       mp  $a |- Q $.
    $}
$( Prove a theorem $)
    th1 $p |- t = t $=
  $( Here is its proof: $)
       tt tze tpl tt weq tt tt weq tt a2 tt tze tpl
       tt weq tt tze tpl tt weq tt tt weq wim tt a2
       tt tze tpl tt tt a1 mp mp
     $.
    """

match verify_file @"C:\mmj2jar\library\setu.mm" with
| Success _ -> printfn "Verification finished successfully."
| Failure(msg,b,c) -> printfn "%s" msg

