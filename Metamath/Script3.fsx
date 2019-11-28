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
| ExprBlock of MetamathExpr []

let is_label c = isAsciiLetter c || isDigit c || c = '-' || c = '_' || c = '.'
let is_math_symbol c = '!' <= c && c <= '~' && c <> '$'

let label s = (many1SatisfyL is_label "Ascii letter, digit, `-`, `_` or `.`") s
let math_symbol s = (many1SatisfyL is_math_symbol "Ascii character between `!` and `~` (excluding `$`.)") s

let terminal x s = (skipString x >>. (spaces1 <|> eof)) s
let skip_string x s = (skipString x >>. spaces1) s 
let file_include s = between (skip_string "$[") (terminal "$]") (label |>> ExprFileInclude .>> spaces1) s

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

let vars s = (between (skip_string "$v") (terminal "$.") (many1_array (var .>> spaces1)) |>> ExprV) s
let cons s = (between (skip_string "$c") (terminal "$.") (many1_array (con .>> spaces1)) |>> ExprC) s

let is_label_inactive x u = (Set.contains x u.labels_hypothesis || Set.contains x u.labels_assertion || Set.contains x u.vars || Set.contains x u.cons) = false

let active_constant s = (math_symbol >>= proceed_if_active (fun x u -> Set.contains x u.cons)) s
let active_variable s = (math_symbol >>= proceed_if_active (fun x u -> Set.contains x u.vars)) s
let floating_variable s = (math_symbol >>= proceed_if_active (fun x u -> Set.contains x u.vars_floating)) s
let floating_math_symbol s = (math_symbol >>= proceed_if_active (fun x u -> Set.contains x u.vars_floating || Set.contains x u.cons)) s
let active_label s = (label >>= proceed_if_active (fun x u -> Set.contains x u.labels_hypothesis || Set.contains x u.labels_assertion)) s

let er_label_is_active label = er (sprintf "Label %s is already active." label)
let check_floating var on_succ u =
    if Set.contains var u.vars_floating then on_succ {u with vars_floating=Set.add var u.vars_floating}
    else er (sprintf "There may not be two active $f statements containing the same variable %s." var)
let check_labels_floating label con on_succ u =
    match Map.tryFind label u.labels_floating with
    | Some con' -> if con = con' then on_succ u else er (sprintf "Labels for $f statements must have uniform typecode across the database. %s $f %s _ <> %s $f %s _" label con label con')
    | None -> on_succ {u with labels_floating=Map.add label con u.labels_floating}
let pcheck_and_add f x (s : CharStream<_>) : Reply<_> = f x (fun u -> s.UserState <- u; Reply(x)) s.UserState

type IsWrap = NoWrap | Wrap
type IsAssertion = Hypothesis | Assertion

let inline add_label is_wrap is_assertion p label (s : CharStream<_>) =
    let inline update_user_state r = 
        let u = s.UserState
        match is_assertion with
        | Hypothesis -> s.UserState <- {u with labels_hypothesis=Set.add label u.labels_hypothesis}
        | Assertion -> s.UserState <- {u with labels_assertion=Set.add label u.labels_assertion}
        r
    match is_wrap with
    | Wrap -> update_user_state (p s) 
    | NoWrap -> update_user_state (); p s

let floating label s = 
    add_label NoWrap Hypothesis (
        skip_string "$f" >>.
        pipe2 
            (active_constant >>= pcheck_and_add (check_labels_floating label) .>> spaces1) 
            (active_variable >>= pcheck_and_add check_floating .>> spaces1 .>> terminal "$.") 
            (fun con var -> ExprF(label,con,var))
        ) label s

let essential label s =
    add_label NoWrap Hypothesis (
        skip_string "$e" >>.
        pipe2 (active_constant .>> spaces1) 
            (many_array (floating_variable .>> spaces1) .>> terminal "$.") 
            (fun c v -> ExprE(label,c,v)) 
        ) label s

let disjoint s = 
    between (skip_string "$d") (terminal "$.") 
        (pipe2 (active_variable .>> spaces1) (many1 (active_variable .>> spaces1))
        (fun a b -> ExprD(a::b |> List.toArray))) s

let axiom label s = 
    add_label NoWrap Assertion (
        skip_string "$a" >>.
        pipe2 (active_constant .>> spaces1) (many_array (floating_math_symbol .>> spaces1) .>> terminal "$.") (fun b c -> ExprA(label,b,c))
        ) label s

let proof label s = 
    add_label Wrap Assertion (
        skip_string "$p" >>.
        pipe3 (active_constant .>> spaces1) 
            (many_array (floating_math_symbol .>> spaces1) .>> skip_string "$=") 
            (many_array (active_label .>> spaces1) .>> terminal "$.") (fun con syms labels -> ExprP(label,con,syms,labels))
        ) label s

let block next s =
    let f next (s : CharStream<_>) = 
        let u = s.UserState
        let r = next s
        s.UserState <- {s.UserState with vars=u.vars; vars_floating=u.vars_floating; labels_hypothesis=u.labels_hypothesis}
        r
    between (skip_string "${") (terminal "$}") (f (many_array next) |>> ExprBlock) s

let comment s = 
    let rec body s = (charsTillString "$" true System.Int32.MaxValue >>. (skipChar ')' <|> (skipChar '(' >>. body >>. body) <|> body)) s
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