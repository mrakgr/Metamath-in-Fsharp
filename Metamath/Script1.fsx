#if INTERACTIVE
#r @"..\packages\FParsec.1.1.0-RC\lib\net45\FParsecCS.dll"
#r @"..\packages\FParsec.1.1.0-RC\lib\net45\FParsec.dll"
#endif
open FParsec

type MetamathTok =
| TokC
| TokV
| TokD
| TokF
| TokE
| TokA
| TokP
| TokProof
| TokDot
| TokBlockStart
| TokBlockEnd
| TokFileStart
| TokFileEnd
| TokString of string
// Comments are ignored during parsing.

let keyword s =
    let f = function
        | 'c' -> preturn TokC 
        | 'v' -> preturn TokV 
        | 'd' -> preturn TokD 
        | 'f' -> preturn TokF 
        | 'e' -> preturn TokE 
        | 'a' -> preturn TokA 
        | 'p' -> preturn TokP 
        | '=' -> preturn TokProof
        | '.' -> preturn TokDot
        | '{' -> preturn TokBlockStart
        | '}' -> preturn TokBlockEnd
        | '[' -> preturn TokFileStart
        | ']' -> preturn TokFileEnd
        | _ -> fun _ -> Reply(Error, expected "'c', 'v', 'd', 'f', 'e', 'a', 'p', '=', '.', '{', '}', '[' or ']'.")

    (skipChar '$' >>. anyChar >>= f .>> spaces1) s

let comment next s = (skipString "$(" >>. skipCharsTillString "$)" true System.Int32.MaxValue >>. spaces1 >>. next) s
let label s = (many1SatisfyL (fun c -> '!' <= c && c <= '~' && c <> '$') "Ascii character between `!` and `~` (excluding `$`.)" |>> TokString .>> spaces1) s
let rec token s = (comment token <|> keyword <|> label) s
let token_array s =
    Inline.Many(
                elementParser = token,
                stateFromFirstElement = (fun x0 ->
                    let ra = ResizeArray<_>()
                    ra.Add(x0)
                    ra),
                foldState = (fun ra x -> ra.Add(x); ra),
                resultFromState = (fun ra -> ra.ToArray())
                ) s

let parser s = token_array s
