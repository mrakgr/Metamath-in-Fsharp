﻿open System.Collections.Generic

#if INTERACTIVE
#r @"..\packages\FParsec.1.1.0-RC\lib\net45\FParsecCS.dll"
#r @"..\packages\FParsec.1.1.0-RC\lib\net45\FParsec.dll"
#endif
open FParsec

/// Types

type Label = int
type Labels = Set<Label>
type Disjoints = Map<string,Set<string>>
type Symbol = Constant of string | Variable of string
type Symbols = Symbol []

type Statement =
    | Floating of string * string
    | Essential of string * Symbols * Disjoints
    | Axiom of string * Symbols * Disjoints * Statement [] 
    | Proof of string * Symbols * Disjoints * Statement []

/// Parsing

type State = {
    // Local
    disjoints : Disjoints
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
        if Map.containsKey x a then s.UserState <- {u with vars=Map.add x None a}; Reply(())
        else er (sprintf "Variable %s is already active." x)
        ) s

let con s = 
    (math_symbol >>= fun x s -> 
        let u = s.UserState
        let a = u.cons
        if a.Contains x then a.Add x |> ignore; Reply(x)
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
let floating_math_symbol s = 
    (math_symbol >>= fun x s ->
        let u : State = s.UserState
        if u.cons.Contains x then Reply(Constant x)
        else match Map.tryFind x u.vars with
             | Some(Some t) -> Reply(Variable x)
             | _ -> er (sprintf "%s is neither a constant nor an active variable" x)
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
            {u with vars=Map.add label (Some tag) u.vars}
            )
    ) s

let free_vars (u : State) ar =
    Array.fold (fun s -> function
        | Variable x -> match u.vars.[x] with Some t -> Set.add t s | _ -> s
        | Constant _ -> s
        ) Set.empty ar

let essential label s =
    (
    skip_string "$e" >>.
    tuple2 (active_constant .>> spaces1) (many_array (floating_math_symbol .>> spaces1) .>> terminal "$.") 
    >>= fun (c, v) -> updateUserState (fun u -> 
        let tag = tag_create u label
        u.statements.Add(tag,Essential(c,v,u.disjoints))
        {u with essentials=free_vars u v + Set.add tag u.essentials}
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
    tuple2 (active_constant .>> spaces1) (many_array (floating_math_symbol .>> spaces1))
    >>= fun (c,sym_seq) -> modifyUserState (fun u -> 
        let tag = tag_create u label
        u.statements.Add(tag,Axiom(c,sym_seq,u.disjoints,labels_to_statements u (free_vars u sym_seq + u.essentials)))
        )
    >>. terminal "$." 
    ) s

let active_label s = (label >>= proceed_if_active (fun x u -> u.labels.ContainsKey x)) s

let print_body (c, v) = 
    let strip x = Array.map (function Variable x | Constant x -> x) x
    [|[|c|]; strip v|] |> Array.concat |> String.concat " "
let error_typecode c c' = sprintf "Unification failed. Typecode %s <> %s" c c'
let error_body a b = sprintf "Unification failed. %s <> %s" (print_body a) (print_body b)

let proof label s = 
    
    /// Proving
    let prove (stack : Stack<_>) x on_succ on_fail = 
        let prove_mandatory m hyp item on_succ on_fail =
            let substitute (m : Map<string, Symbols>) (desc : Symbols) =
                let subvars = Dictionary(HashIdentity.Structural)
                subvars,
                Array.collect (function
                    | Variable x as x' ->
                        match Map.tryFind x m with
                        | Some v ->
                            match subvars.TryGetValue x with
                            | false, _ -> subvars.[x] <- Array.fold (fun s -> function Variable x -> Set.add x s | Constant _ -> s) Set.empty v
                            | true, _ -> ()
                            v
                        | None -> [|x'|]
                    | Constant _ as x' -> [|x'|]
                    ) desc

            let disjointness_check (disjoint_vars : Map<string, Set<string>>) (substs_map : Dictionary<string, Set<string>>) =
                let fails = ResizeArray()

                let check (kv : KeyValuePair<_,_>) next prev = 
                    let var', subvars' as cur = kv.Key, kv.Value
                    match prev with
                    | None -> ()
                    | Some (var, subvars) as prev ->
                        Set.iter (fun v ->
                            let v_disjoint_vars =
                                match Map.tryFind v disjoint_vars with
                                | None -> Set.empty
                                | Some v_disjoint_vars -> v_disjoint_vars
                            if Set.isEmpty (subvars' - v_disjoint_vars) = false then fails.Add((var,v),(var',subvars'))
                            ) subvars
                        next prev
                    next (Some cur)

                Seq.foldBack check substs_map (fun _ -> ()) None
                fails.ToArray()

            match hyp, item with
            | Floating(c,v),(c',v') -> if c = c' then on_succ (Map.add v v' m) else on_fail (error_typecode c c')
            | Essential(c,sym_seq,disjoint),(c',sym_seq') -> 
                if c = c' then
                    let substituted_vars, sym_seq = substitute m sym_seq
                    if sym_seq = sym_seq' then 
                        let r = disjointness_check disjoint substituted_vars
                        if Array.isEmpty r then on_succ m
                        else 
                            Array.map (fun ((var,v),(var',subvars)) -> sprintf "The disjointness check for %s and %s failed. %s does not interstect %A" var var' v subvars) r
                            |> String.concat "\n"
                            |> on_fail
                    else
                        on_fail (error_body (c,sym_seq) (c', sym_seq'))
                else on_fail (error_typecode c c')
            | _ -> failwith "impossible"

        match x with
        | Floating(c,v) -> stack.Push(c,[|Variable v|]); on_succ()
        | Essential _ -> on_fail "Essential hypotheses are not directly usable."
        | Proof(con,sym_seq,disjoint,hyps) | Axiom(con,sym_seq,disjoint,hyps) when hyps.Length > stack.Count -> on_fail "Not enough hypotheses on stack."
        | Proof(con,sym_seq,disjoint,hyps) | Axiom(con,sym_seq,disjoint,hyps) ->
            let stack_items = Array.zeroCreate hyps.Length
            let rec pop i = if i > 0 then stack_items.[i-1] <- stack.Pop(); pop (i-1) else ()
            pop hyps.Length
        
            let rec loop i s = 
                if i < hyps.Length then prove_mandatory s hyps.[i] stack_items.[i] (loop (i+1)) (on_fail << sprintf "(error for item %i out of %i) %s" (i+1) hyps.Length)
                else on_succ()
            loop 0 Map.empty

    (
    skip_string "$p" >>.
    tuple2 (active_constant .>> spaces1) (many_array (floating_math_symbol .>> spaces1)) 
    .>> skip_string "$="
    >>= fun (c,sym_seq) ->
        let stack = Stack()
        let prove hyp = prove stack hyp (fun () -> Reply(())) er
        let prove_label label (s : CharStream<State>) = let u = s.UserState in prove u.statements.[u.labels.[label]]
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
                u.statements.Add(tag,Proof(c,sym_seq,u.disjoints,labels_to_statements u (free_vars u sym_seq + u.essentials)))
                )
    >>. terminal "$."
    ) s

let block next s =
    let f next (s : CharStream<_>) = 
        let u = s.UserState
        let r = next s
        s.UserState <- {s.UserState with vars=u.vars; disjoints=u.disjoints; essentials=u.essentials}
        r
    between (skip_string "${") (terminal "$}") (f (skipMany next)) s

let comment s = 
    let rec body s = (charsTillString "$" true System.Int32.MaxValue >>. (skipChar ')' <|> (skipChar '(' >>. fail "Nested comments are not allowed.") <|> body)) s
    (skipString "$(" >>. body >>. (spaces1 <|> eof)) s

let checked_label s = 
    let proceed_if_inactive_label label (s : CharStream<_>) =
        if s.UserState.labels.ContainsKey label = false then Reply(label)
        else er_label_is_active label
    (label >>= proceed_if_inactive_label) s

let rec parser s =
    let rec body s = 
        choice [|
            checked_label >>= fun label -> spaces1 >>. choice [|floating label; essential label; axiom label; proof label|]
            vars; disjoint; comment >>. body; block body
            |] s

    (skipMany (choice [|cons; file_include; body|] .>> eof)) s

and file_include (s : CharStream<_>) =
    (
    label >>= fun x s ->
        match runParserOnFile parser s.UserState "" System.Text.Encoding.Default with
        | Success(r,u,_) -> s.UserState <- u; Reply(r)
        | Failure(msg,_,_) -> er msg
    ) s

