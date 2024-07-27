{

let lineno   = ref 1
and start    = ref 0
and filename = ref ""

(* To handle glyphs *)
let curr_offset = ref 0

let create inFile stream =
  if not (Filename.is_implicit inFile) then filename := inFile
  else filename := Filename.concat (Sys.getcwd()) inFile;
  lineno := 1; start := 0; Lexing.from_channel stream

let from_string s =
  filename := ""; lineno := 1; start := 0;
  Lexing.from_string s

let newline lexbuf = incr lineno; curr_offset := 0; start := (Lexing.lexeme_start lexbuf)

}

let whitespace = [' ' '	']
let idchar =  ['A'-'Z' 'a'-'z' '_' '0'-'9' '\'']

let lident = ['a'-'z'] idchar*
let uident = ['A'-'Z'] idchar*

let comment = ['#'] [^'\n'] *

rule main = parse
  whitespace+                       { main lexbuf }
| whitespace*("\r")?"\n"            { newline lexbuf; main lexbuf }
| comment                           { main lexbuf }

| ","                               { Parser.COMMA }
| "="                               { Parser.EQUALS }
| "("                               { Parser.LPAREN }
| ")"                               { Parser.RPAREN }
| "_"                               { Parser.UNDERSCORE }

| "->"                              { Parser.IMPLIES }
| "|"                              { Parser.OR }
| "&"                              { Parser.AND }
| "~"                              { Parser.NOT }

| "assume" { Parser.ASSUME }
| "fantasy" { Parser.FANTASY }
| "add_doubleneg" { Parser.DNEG_ADD }
| "rem_doubleneg" { Parser.DNEG_REM }
| "join" { Parser.JOIN }
| "separate" { Parser.SEPARATE }
| "contrapositive1" { Parser.CONTRAPOSITIVE1 }
| "contrapositive2" { Parser.CONTRAPOSITIVE2 }
| "detachment" { Parser.DETACHMENT }
| "switcheroo" { Parser.SWITCHEROO }
| "de_morgan" { Parser.DE_MORGAN }

| lident as id { Parser.LIDENT id }
| uident as id  { Parser.UIDENT id }

| eof { Parser.EOF }
| _ as c { failwith (Printf.sprintf "unexpected character: %C" c) }

