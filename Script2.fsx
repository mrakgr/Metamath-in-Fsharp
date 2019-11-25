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
| ExprA of label : string * con : string * var_seq : string []
| ExprP of label : string * con : string * var : string [] * label_seq : string []
| ExprFileInclude of file : string

let is_label c = isAsciiLetter c || isDigit c || c = '-' || c = '_' || c = '.'
let is_math_symbol c = '!' <= c && c <= '~' && c <> '$'

let label s = many1SatisfyL is_label "Ascii letter, digit, `-`, `_` or `.`" s
let math_symbol s = many1SatisfyL is_math_symbol "Ascii character between `!` and `~` (excluding `$`.)" s

let file_include s = between (skipString "$[" >>. spaces1) (skipString "$]" >>. spaces1) (label |>> ExprFileInclude .>> spaces1) s

type State = {
    cons : Set<string>
    vars : Set<string>
    }

let inline checkUpdateUserState check on_succ on_fail (s : CharStream<_>) =
    if check s.UserState then updateUserState on_succ s else on_fail s

let inline addIfUndeclared get set x s =
    (checkUpdateUserState (fun u -> Set.contains x (get u) = false) 
        (fun (u : State) -> set u (Set.add x (get u))) 
        (fun s -> Reply(FatalError, messageError <| sprintf "%s cannot be declared twice." x))
     >>. preturn x) s

let var s = (math_symbol >>= addIfUndeclared (fun u -> u.vars) (fun u x -> {u with vars=x})) s
let con s = (math_symbol >>= addIfUndeclared (fun u -> u.cons) (fun u x -> {u with cons=x})) s

let vars s = (between (skipString "$v" >>. spaces1) (skipString "$." >>. spaces) (many1 var) |>> (List.toArray >> ExprV)) s
let cons s = (between (skipString "$c" >>. spaces1) (skipString "$." >>. spaces) (many1 con) |>> (List.toArray >> ExprC)) s