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
    labels : Set<string>
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


let inline add_if_undeclared' check get set x (s : CharStream<_>) =
    let u = s.UserState
    let a = get u
    if check x u then s.UserState <- set u (Set.add x a); Reply(x)
    else Reply(FatalError, messageError <| sprintf "%s cannot be declared twice." x)

let inline add_if_undeclared get set x s = add_if_undeclared' (fun x u -> Set.contains x (get u)) get set x s

let inline proceed_if_active check x (s : CharStream<_>) =
    if check s.UserState x then Reply(x)
    else Reply(FatalError, messageError <| sprintf "%s must be active." x)

let var s = (math_symbol >>= add_if_undeclared (fun u -> u.vars) (fun u x -> {u with vars=x})) s
let con s = (math_symbol >>= add_if_undeclared (fun u -> u.cons) (fun u x -> {u with cons=x})) s

let vars s = (between (skipString "$v") (skipString "$.") (many1_array var) |>> ExprV) s
let cons s = (between (skipString "$c") (skipString "$.") (many1_array con) |>> ExprC) s

let inactive_label s = 
    let check x u = (Set.contains x u.labels || Set.contains x u.vars || Set.contains x u.cons) = false
    (label >>= add_if_undeclared' check (fun u -> u.labels) (fun u x -> {u with labels=x})) s
let active_constant s = (math_symbol >>= proceed_if_active (fun u x -> Set.contains x u.cons)) s
let active_variable s = (math_symbol >>= proceed_if_active (fun u x -> Set.contains x u.vars)) s
let active_math_symbol s = (math_symbol >>= proceed_if_active (fun u x -> Set.contains x u.vars || Set.contains x u.cons)) s
let active_label s = (label >>= proceed_if_active (fun u x -> Set.contains x u.labels)) s
let floating s = pipe3 (inactive_label .>> skipString "$f") active_constant (active_variable .>> skipString "$.") (fun l c v -> ExprF(l,c,v)) s
let essential s = pipe3 (inactive_label .>> skipString "$e") active_constant (many_array active_variable .>> skipString "$.") (fun l c v -> ExprE(l,c,v)) s 
let disjoint s = between (skipString "$d") (skipString "$.") (pipe2 active_variable (many1 active_variable) (fun a b -> ExprD(a::b |> List.toArray))) s
let axiom s = pipe3 (inactive_label .>> skipString "$a") active_constant (many_array active_math_symbol .>> skipString "$.") (fun a b c -> ExprA(a,b,c)) s
let proof s = 
    pipe4 (inactive_label .>> skipString "$p") active_constant (many_array active_math_symbol .>> skipString "$=") 
        (many_array active_label) (fun label con syms labels -> ExprP(label,con,syms,labels)) s

