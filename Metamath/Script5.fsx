﻿open System.Collections.Generic

#if INTERACTIVE
#r @"..\packages\FParsec.1.1.0-RC\lib\net45\FParsecCS.dll"
#r @"..\packages\FParsec.1.1.0-RC\lib\net45\FParsec.dll"
#endif
open FParsec

type Label = int
type Labels = Set<Label>
type Disjoints = Map<string,Set<string>>
type Symbol = Constant of string | Variable of string
type Symbols = Symbol []

type Statement =
    | Floating of string * string
    | Essential of string * Symbols * Disjoints
    | Axiom of string * Symbols * Disjoints * Statement list 
    | Proof of string * Symbols * Disjoints * Statement list

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

let tag (x : State) v = x.labels.[v]
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

//let is_label_inactive x u = (Set.contains x u.labels_hypothesis || Set.contains x u.labels_assertion || Set.contains x u.vars || Set.contains x u.cons) = false
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
let check_floating var (s : CharStream<_>) =
    if is_floating_var var s.UserState = false then Reply(var)
    else er (sprintf "There may not be two active $f statements containing the same variable %s." var)

let floating label s = 
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

let modifyUserState f (s: CharStream<_>) = f s.UserState; Reply(())

let disjoint_constraints (u : State) free_vars =
    let f x' next s = function 
        | None -> next s (Some x')
        | Some x as prev ->
            match Map.tryFind x u.disjoints with
            | Some d -> if Set.contains x' d then (x,x') :: s else s
            | None -> s
            |> fun s -> next (next s prev) (Some x')
    Set.foldBack f free_vars (fun s _ -> s) [] None


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
    between (skip_string "$d") (terminal "$.") 
        (skipMany (active_variable >>= (fun x -> check (h.Add(x)) (sprintf "%s cannot be disjoint with itself." x)) >>. spaces1))
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
    ) s

let labels_to_statements (u : State) x = Set.toList x |> List.map (fun x -> u.statements.[x])
        
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

let prove_label stack' label (s : CharStream<State>) =
    let u = s.UserState
    match u.statements.[u.labels.[label]] with
    | Floating(c,v) -> stack' := (c,[|v|]) :: !stack'; Reply(())
    | Essential _ -> er "Essential hypotheses are not directly usable."
    | Axiom(con,sym_seq,disjoint,hyps) | Proof(con,sym_seq,disjoint,hyps) ->
        let rec loop_unify m stack = function
            | (Floating(c,v),(c',v')) :: ops -> if c = c' then loop_unify (Map.add v v' m) stack ops else er (sprintf "Unification failed. Typecode %s <> %s" c c')
            | (Essential(c,sym_seq,disjoint),(c',sym_seq')) :: ops -> 
                if c = c' then
                    let sym_seq = substitute m sym_seq
                    if sym_seq = sym_seq' then disjointness_check disjoint
                    else er "Unification failed."
                else er (sprintf "Unification failed. Typecode %s <> %s" c c')
            | [] -> stack' := (con, substitute m sym_seq') :: stack; Reply(())
            | _ -> failwith "impossible"

        let rec loop_init ops hyps stack =
            match hyps, stack with
            | [], stack -> loop_unify Map.empty stack ops
            | (h :: h'), (d :: d') -> loop_init ((u.statements.[h],d) :: ops) h' d'
            | _, [] -> er "Not enough hypotheses on the stack."

        let hyps = Set.fold (fun b a -> a :: b) [] hyps
        loop_init [] hyps !stack'
        

let proof label s = 
    (
    skip_string "$p" >>.
    tuple2 (active_constant .>> spaces1) (many_array (floating_math_symbol .>> spaces1)) 
    .>> skip_string "$="
    >>= fun (c,v) -> 
        let stack = ref []
        let prove_label = fun label s -> failwith ""
        let prove_finish s =
            let concat (c,v) = sprintf "%s %s" c (String.concat " " v)
            match !stack with
            | [c',v'] -> if c <> c' || v <> v' then er (sprintf "Unification failed. The expression %s fails to prove the proof %s" (concat (c,v)) (concat (c',v'))) else Reply(())
            | l -> 
                List.map concat l
                |> String.concat "\n"
                |> sprintf "Unification failed. A single term must be left at the end of the proof. Got:\n%s"
                |> er

        (skipMany (active_label >>= prove_label >>. spaces1) >>. prove_finish)
    >>. terminal "$."
    ) s

let block next s =
    let f next (s : CharStream<_>) = 
        let u = s.UserState
        let r = next s
        s.UserState <- {s.UserState with vars=u.vars; vars_floating=u.vars_floating; labels_hypothesis=u.labels_hypothesis}
        r
    between (skip_string "${") (terminal "$}") (f (many_array next) |>> ExprBlock) s

let comment s = 
    let rec body s = (charsTillString "$" true System.Int32.MaxValue >>. (skipChar ')' <|> (skipChar '(' >>. fail "Nested comments are not allowed.") <|> body)) s
    (skipString "$(" >>. body >>. (spaces1 <|> eof)) s

let proceed_if_inactive_label label (s : CharStream<_>) =
    if is_label_inactive label s.UserState then Reply(label)
    else er_label_is_active label
let checked_label s = (label >>= proceed_if_inactive_label) s

let parser s =
    let rec body s = 
        choice [|
            checked_label >>= fun label -> spaces1 >>. choice [|floating label; essential label; axiom label; proof label|]
            vars; disjoint; comment >>. body; block body; file_include
            |] s

    (many_array (cons <|> body) |>> ExprBlock .>> eof) s