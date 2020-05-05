open! Stdio
open ScribbleCodeGen

let usage =
  "\nUSAGE: " ^ Sys.argv.(0)
  ^ " [--help] --protocol <string> --role <string> [--output <string>] \
     [--recursion] <string>\n\n\
     FILENAME:\n\n\
    \    <string>              Path to Scribble Output\n\n\
     OPTIONS:\n\n\
    \    --protocol <string>   Name of Scribble Protocol\n\
    \    --role <string>       Name of Local Role in the Protocol\n\
     Style\n\
    \    --output, -o <string> Path to Output Filename\n\
    \    --recursion           Allow Refinements on Recursion (Scribble \
     dev-assrt)\n\
    \    --help                display this list of options.\n"

let protocol = ref ""

let role = ref ""

let err msg = print_string msg ; print_string usage ; exit 1

(* let handle_mode = function *)
(* | "legacyapi" -> mode := Types.LegacyApi *)
(* | "eventapi" -> mode := Types.EventApi *)
(* | "fstar" -> mode := Types.FStar *)
(* | _ -> err "Error: Unknown mode\n" *)
(*  *)

let handle_mode _ = Printf.eprintf "--mode is deprecated, defaulting to F*\n"

let speclist =
  [ ("--protocol", Arg.Set_string protocol, "Name of Scribble Protocol")
  ; ("--role", Arg.Set_string role, "Name of Local Role in the Protocol")
  ; ("--mode", Arg.String handle_mode, "Mode of Code Generation")
  ; ( "--output"
    , Arg.Set_string CodePrinter.fileName
    , "Path to Output Filename" )
  ; ("-o", Arg.Set_string CodePrinter.fileName, "Path to Output Filename") ]

let () =
  let run filename =
    if !protocol = "" then err "Error: Protocol not set" ;
    if !role = "" then err "Error: Role not set" ;
    if filename = "" then err "Error: File not set" ;
    Lib.processScribbleOutput filename !protocol !role
  in
  Arg.parse speclist run usage
