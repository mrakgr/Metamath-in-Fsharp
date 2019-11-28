#if INTERACTIVE
#r @"..\packages\FParsec.1.1.0-RC\lib\net45\FParsecCS.dll"
#r @"..\packages\FParsec.1.1.0-RC\lib\net45\FParsec.dll"
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

let inline er x = Reply(Error, messageError x)
let inline proceed_if_active check x (s : CharStream<_>) = 
    if check x s.UserState then Reply(x)
    else er (sprintf "%s must be active." x)

let add_if_inactive get set x (s : CharStream<_>) =
    let u = s.UserState
    let a = get u
    if Set.contains x a then s.UserState <- set u (Set.add x a); Reply(x)
    else er (sprintf "%s is already active." x)

let var s = (math_symbol >>= add_if_inactive (fun u -> u.vars) (fun u x -> {u with vars=x})) s
let con s = (math_symbol >>= add_if_inactive (fun u -> u.cons) (fun u x -> {u with cons=x})) s

let vars s = (between (skipString "$v") (skipString "$.") (many1_array var) |>> ExprV) s
let cons s = (between (skipString "$c") (skipString "$.") (many1_array con) |>> ExprC) s

let is_label_inactive x u = (Set.contains x u.labels_hypothesis || Set.contains x u.labels_assertion || Set.contains x u.vars || Set.contains x u.cons) = false

let active_constant s = (math_symbol >>= proceed_if_active (fun x u -> Set.contains x u.cons)) s
let active_variable s = (math_symbol >>= proceed_if_active (fun x u -> Set.contains x u.vars)) s
let floating_variable s = (math_symbol >>= proceed_if_active (fun x u -> Set.contains x u.vars_floating)) s
let floating_math_symbol s = (math_symbol >>= proceed_if_active (fun x u -> Set.contains x u.vars_floating || Set.contains x u.cons)) s
let active_label s = (label >>= proceed_if_active (fun x u -> Set.contains x u.labels_hypothesis)) s

let er_label_is_active label = er (sprintf "Label %s is already active." label)
let check_inactive_label label on_succ u =
    if is_label_inactive label u then on_succ {u with labels_hypothesis=Set.add label u.labels_hypothesis}
    else er_label_is_active label
let check_floating var on_succ u =
    if Set.contains var u.vars_floating then on_succ {u with vars_floating=Set.add var u.vars_floating}
    else er (sprintf "There may not be two active $f statements containing the same variable %s." var)
let check_labels_floating label con on_succ u =
    match Map.tryFind label u.labels_floating with
    | Some con' -> if con = con' then on_succ u else er (sprintf "Labels for $f statements must have uniform typecode across the database. %s $f %s _ <> %s $f %s _" label con label con')
    | None -> on_succ {u with labels_floating=Map.add label con u.labels_floating}
let pcheck_and_add f x (s : CharStream<_>) : Reply<_> = f x (fun u -> s.UserState <- u; Reply(x)) s.UserState

let floating label s = 
    (
    pcheck_and_add check_inactive_label label >>.
    pipe2 
        (skipString "$f" >>. active_constant >>= pcheck_and_add (check_labels_floating label)) 
        (active_variable >>= pcheck_and_add check_floating .>> skipString "$.") 
        (fun con var -> ExprF(label,con,var))
    ) s

let essential label s = pipe3 (pcheck_and_add check_inactive_label label .>> skipString "$e") active_constant (many_array floating_variable .>> skipString "$.") (fun l c v -> ExprE(l,c,v)) s 
let disjoint s = between (skipString "$d") (skipString "$.") (pipe2 active_variable (many1 active_variable) (fun a b -> ExprD(a::b |> List.toArray))) s

let add_label_if_inactive is_add_after label p (s : CharStream<_>) =
    if is_label_inactive label s.UserState then
        let inline update_user_state r = 
            let u = s.UserState
            s.UserState <- {u with labels_assertion=Set.add label u.labels_assertion}
            r
        if is_add_after then update_user_state (p s)
        else update_user_state (); p s
    else
        er_label_is_active label

let axiom label s = 
    add_label_if_inactive false label (
        skipString "$a" >>.
        pipe2 active_constant (many_array floating_math_symbol .>> skipString "$.") (fun b c -> ExprA(label,b,c))
        ) s

let proof label s = 
    (
    add_label_if_inactive true label (
        skipString "$p" >>.
        pipe3 active_constant (many_array floating_math_symbol .>> skipString "$=") 
            (many_array active_label) (fun con syms labels -> ExprP(label,con,syms,labels))
        )
    ) s

let block next s =
    let f next (s : CharStream<_>) = 
        let u = s.UserState
        let r = next s
        s.UserState <- {s.UserState with vars=u.vars; vars_floating=u.vars_floating; labels_hypothesis=u.labels_hypothesis}
        r
    between (skipString "${") (skipString "$}") (f next) s
