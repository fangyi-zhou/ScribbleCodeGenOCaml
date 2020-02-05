{
  open Lexing
  open ExprParser
}

let smallalpha = ['a'-'z']
let capalpha = ['A'-'Z']
let alpha = smallalpha | capalpha
let digit = ['0'-'9']
let alphanum = alpha | digit
let alphanum_underscore = alphanum | '_'
let variable = alpha alphanum_underscore*
let whitespace = [' ' '\t']
let newline = ('\n' | '\r' '\n')

rule token = parse
| whitespace  { token lexbuf }
| newline { token lexbuf }
| "(" { LPAREN }
| ")" { RPAREN }
| "{" { LBRACE }
| "}" { RBRACE }
| ":" { COLON }
| "->" { RIGHTARROW }
| "+" { PLUS }
| "-" { MINUS }
| "=" { EQUAL }
| "&&" { AND }
| "||" { OR }
| ">=" { GREATEREQUAL }
| "<=" { LESSEQUAL }
| "<>" { NOTEQUAL }
| ">" { GREATER }
| "<" { LESS }
| "|" { BAR }
| "$" { DOLLAR }
| "not" { NOT }
| "true" { TRUE }
| "false" { FALSE }
| variable { ID(lexeme lexbuf) }
| ['-']?digit+ { INT(Base.Int.of_string(lexeme lexbuf)) }
| eof { EOF }