#if INTERACTIVE
#r @"packages\FParsec.1.1.0-RC\lib\net45\FParsecCS.dll"
#r @"packages\FParsec.1.1.0-RC\lib\net45\FParsec.dll"
#endif
open FParsec

type MetamathExpr =
| ExprC of string []
| ExprV of string []
| ExprD of string []
| ExprF of label : string * con : string * var : string
| ExprE of label : string * con : string * var_seq : string []
| ExprA of label : string * con : string * math_symbol_seq : string []
| ExprP of label : string * con : string * math_symbol_seq : string [] * label_seq : string []
| ExprFileInclude of file : string

let is_label c = isAsciiLetter c || isDigit c || c = '-' || c = '_' || c = '.'
let is_math_symbol c = '!' <= c && c <= '~' && c <> '$'

let label s = (many1SatisfyL is_label "Ascii letter, digit, `-`, `_` or `.`" .>> spaces1) s
let math_symbol s = (many1SatisfyL is_math_symbol "Ascii character between `!` and `~` (excluding `$`.)" .>> spaces1) s

let skipString x s = (skipString x >>. spaces1) s 
let file_include s = between (skipString "$[") (skipString "$]") (label |>> ExprFileInclude) s

type State = {
    cons : Set<string>
    vars : Set<string>
    vars_floating : Set<string>
    labels_hypothesis : Set<string>
    labels_assertion : Set<string>
    labels_floating : Map<string, string>
    }

let many_array_first_elem x0 = let ra = ResizeArray<_>() in ra.Add(x0); ra
let many_array_fold_state (ra : ResizeArray<_>) x = ra.Add(x); ra
let many_array_result_from_state (ra : ResizeArray<_>) = ra.ToArray()
let many1_array p s =
    Inline.Many(elementParser = p, stateFromFirstElement = many_array_first_elem, foldState = many_array_fold_state,
                resultFromState = many_array_result_from_state) s
let many_array p s =
    Inline.Many(elementParser = p, stateFromFirstElement = many_array_first_elem, foldState = many_array_fold_state,
                resultFromState = many_array_result_from_state, resultForEmptySequence = (fun () -> [||])) s

//let inline add_if_checked error check get set x (s : CharStream<_>) =
//    let u = s.UserState
//    if check x u then s.UserState <- set u (Set.add x (get u)); Reply(x)
//    else Reply(Error, messageError <| error x)



let inline proceed_if_checked error check x (s : CharStream<_>) =
    if check x s.UserState then Reply(x)
    else Reply(Error, messageError <| error x)

let inline proceed_if_active check x (s : CharStream<_>) = proceed_if_checked (sprintf "%s must be active.") check x s

let inactive_error x = sprintf "%s is already active." x
let add_if_inactive get set x (s : CharStream<_>) =
    let u = s.UserState
    let a = get u
    if Set.contains x a then s.UserState <- set u (Set.add x a); Reply(x)
    else Reply(Error, messageError <| inactive_error x)

let var s = (math_symbol >>= add_if_inactive (fun u -> u.vars) (fun u x -> {u with vars=x})) s
let con s = (math_symbol >>= add_if_inactive (fun u -> u.cons) (fun u x -> {u with cons=x})) s

let vars s = (between (skipString "$v") (skipString "$.") (many1_array var) |>> ExprV) s
let cons s = (between (skipString "$c") (skipString "$.") (many1_array con) |>> ExprC) s

let label_check x u = (Set.contains x u.labels_hypothesis || Set.contains x u.labels_assertion || Set.contains x u.vars || Set.contains x u.cons) = false

let active_constant s = (math_symbol >>= proceed_if_active (fun x u -> Set.contains x u.cons)) s
let active_variable s = (math_symbol >>= proceed_if_active (fun x u -> Set.contains x u.vars)) s
let floating_variable s = (math_symbol >>= proceed_if_active (fun x u -> Set.contains x u.vars_floating)) s
let floating_math_symbol s = (math_symbol >>= proceed_if_active (fun x u -> Set.contains x u.vars_floating || Set.contains x u.cons)) s
let active_label s = (label >>= proceed_if_active (fun x u -> Set.contains x u.labels_hypothesis)) s

let er x = Reply(Error, messageError x)
let check_inactive_label label on_succ u = // (add_if_inactive' label_check (fun u -> u.labels_hypothesis) (fun u x -> {u with labels_hypothesis=x}) label) s
    if Set.contains label u.labels_hypothesis then on_succ {u with labels_hypothesis=Set.add label u.labels_hypothesis}
    else er (inactive_error label)
let check_floating var on_succ u =
    if Set.contains var u.vars_floating then on_succ {u with vars_floating=Set.add var u.vars_floating}
    else er (sprintf "There may not be two active $f statements containing the same variable %s." var)
let check_labels_floating (label,con) on_succ u =
    match Map.tryFind label u.labels_floating with
    | Some con' -> if con = con' then on_succ u else er (sprintf "Labels for $f statements must have uniform typecode across the database. %s $f %s _ <> %s $f %s _" label con label con'))
    | None -> on_succ {u with labels_floating=Map.add l c u.labels_floating}

let floating label s = 
    (
    tuple2 (skipString "$f" >>. active_constant) (active_variable .>> skipString "$.") 
    >>= fun (con, var) s -> 
        fun u -> s.UserState <- u; Reply(ExprF(label,con,var))
        |> check_labels_floating (label, con)
        |> check_floating var
        |> check_inactive_label label
        |> (|>) s.UserState
    ) s

let essential label s = pipe3 (inactive_label_hypothesis label .>> skipString "$e") active_constant (many_array floating_variable .>> skipString "$.") (fun l c v -> ExprE(l,c,v)) s 
let disjoint s = between (skipString "$d") (skipString "$.") (pipe2 active_variable (many1 active_variable) (fun a b -> ExprD(a::b |> List.toArray))) s
let axiom label s = 
    let label s = (add_if_inactive' label_check (fun u -> u.labels_assertion) (fun u x -> {u with labels_assertion=x}) label) s    
    pipe3 (label .>> skipString "$a") active_constant (many_array floating_math_symbol .>> skipString "$.") (fun a b c -> ExprA(a,b,c)) s
let proof label s = 
    (
    (userStateSatisfies (label_check label) <?> inactive_error label) >>. skipString "$p" >>.
    pipe3 active_constant (many_array floating_math_symbol .>> skipString "$=") 
        (many_array active_label) (fun con syms labels -> ExprP(label,con,syms,labels))
    .>> updateUserState (fun u -> {u with labels_assertion=Set.add label u.labels_assertion}) 
    ) s

let block next s =
    let f next (s : CharStream<_>) = 
        let u = s.UserState
        let r = next s
        s.UserState <- {s.UserState with vars=u.vars; vars_floating=u.vars_floating; labels_hypothesis=u.labels_hypothesis}
        r
    between (skipString "${") (skipString "$}") (f next) s

//type State = {
//    cons : Set<string>
//    vars : Set<string>
//    vars_floating : Set<string>
//    labels_hypothesis : Set<string>
//    labels_assertion : Set<string>
//    labels_floating : Map<string, string>
//    }