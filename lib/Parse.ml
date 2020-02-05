open! Base
open Stdio
open Printf
open Types

let isVariable x = Char.is_alpha x || Char.is_digit x || Char.equal x '_'

let span f xs = (Sequence.take_while ~f xs, Sequence.drop_while ~f xs)

let skipSpaces str = Sequence.drop_while ~f:Char.is_whitespace str

let seqToString (str : char seq) =
  str |> Sequence.to_list |> String.of_char_list

let parseLabel str : label * char seq =
  let label, rest = span isVariable str in
  (seqToString label, rest)

let rec parsePayloadItems str : payload * char seq =
  let str = skipSpaces str in
  if Sequence.is_empty str then ([], str)
  else
    let variable, rest = span isVariable str in
    let rest = skipSpaces rest in
    let rest =
      match Sequence.hd_exn rest with
      | ':' -> Sequence.tl_eagerly_exn rest
      | _ -> failwith "expected ':' in payload"
    in
    let rest = skipSpaces rest in
    let ty, rest = span isVariable rest in
    let payloadItem = (seqToString variable, seqToString ty) in
    let rest = skipSpaces rest in
    match Sequence.hd rest with
    | Some ',' ->
        let rest = Sequence.tl_eagerly_exn rest in
        let restPayloadItems, rest = parsePayloadItems rest in
        (payloadItem :: restPayloadItems, rest)
    | Some _ ->
        failwithf "unexpected item in payloads %s" (seqToString rest) ()
    | None -> ([payloadItem], rest)

let parsePayload str : payload * char seq =
  match Sequence.hd_exn str with
  | '(' ->
      let str = Sequence.tl_eagerly_exn str in
      let items, rest = span (Char.( <> ) ')') str in
      let payload, rest' = parsePayloadItems items in
      if not (Sequence.is_empty rest') then
        eprintf "LeftOver Payloads %s\n" (seqToString rest') ;
      let rest =
        match Sequence.hd_exn rest with
        | ')' -> Sequence.tl_eagerly_exn rest
        | _ -> failwith "unfinished payload, missing ')'"
      in
      (payload, rest)
  | _ -> failwith "invalid payload"

let parseRole str : role * char seq =
  let role, rest = span isVariable str in
  (seqToString role, rest)

let parseAction str : action * char seq =
  match Sequence.hd_exn str with
  | '?' -> (
      let str = Sequence.tl_eagerly_exn str in
      match Sequence.hd_exn str with
      | '?' -> (Accept, Sequence.tl_eagerly_exn str)
      | _ -> (Receive, str) )
  | '!' -> (
      let str = Sequence.tl_eagerly_exn str in
      match Sequence.hd_exn str with
      | '!' -> (Request, Sequence.tl_eagerly_exn str)
      | _ -> (Send, str) )
  | _ -> failwith "invalid action"

let parseOldAssertionString str : string * char seq =
  match Sequence.hd str with
  | Some '@' -> (
      let str = Sequence.tl_eagerly_exn str in
      match Sequence.hd_exn str with
      | '\"' ->
          let str = Sequence.tl_eagerly_exn str in
          let assertion, rest = span (Char.( <> ) '\"') str in
          let rest =
            match Sequence.hd_exn rest with
            | '\"' -> Sequence.tl_eagerly_exn rest
            | _ -> failwith "unfinished assertion, missing '\"'"
          in
          (seqToString assertion, rest)
      | _ -> failwith "invalid assertion, missing '\"'" )
  | Some _ -> failwithf "unknown assertion %s" (seqToString str) ()
  | None ->
      (* No assertion *)
      ("", str)

let fixAssertionDiscrepancy assertions =
  let assertions =
    String.substr_replace_all assertions ~pattern:"True" ~with_:"true"
  in
  let assertions =
    String.substr_replace_all assertions ~pattern:"False" ~with_:"false"
  in
  (* "true" means no assertions *)
  if String.(assertions = "true") then "" else assertions

let parseNewAssertionString str : string * char seq =
  let assertions, rest = span (Char.( <> ) '}') str in
  let assertions =
    match Sequence.hd assertions with
    | Some '{' ->
        let assertions = Sequence.tl_eagerly_exn assertions |> seqToString in
        fixAssertionDiscrepancy assertions
    | _ -> failwith "invalid assertion, missing '{'"
  in
  let rest =
    match Sequence.hd rest with
    | Some '}' -> Sequence.tl_eagerly_exn rest
    | _ -> failwith "unexpected"
  in
  (assertions, rest)

let parseRecVars str : char seq list * char seq =
  match Sequence.hd str with
  | Some '<' ->
      let rec aux str acc =
        let str = skipSpaces str in
        let expr, rest = span (fun c -> Char.(c <> '>' && c <> ',')) str in
        match Sequence.hd rest with
        | Some '>' ->
            let acc = if Sequence.is_empty expr then acc else expr :: acc in
            (List.rev acc, Sequence.tl_eagerly_exn rest)
        | Some ',' -> aux (Sequence.tl_eagerly_exn rest) (expr :: acc)
        | _ -> failwith "Unexpected recursion expression"
      in
      aux (Sequence.tl_eagerly_exn str) []
  | _ -> failwith "invalid recursion variable list, missing '<'"

let parseDotLabelPrefix (str : string) :
    role * action * label * payload * char seq =
  (* let str = str.ToCharArray() |> Sequence.ofArray in *)
  let str = str |> String.to_list |> Sequence.of_list in
  let partner, str = parseRole str in
  let action, str = parseAction str in
  let label, str = parseLabel str in
  let payload, str = parsePayload str in
  (partner, action, label, payload, str)

let parseOldDotLabel (str : string) =
  let partner, action, label, payload, str = parseDotLabelPrefix str in
  let assertion, str = parseOldAssertionString str in
  if not (Sequence.is_empty str) then
    eprintf "Unexpected %s\n" (seqToString str) ;
  (partner, action, label, payload, assertion, [])

let parseNewDotLabel (str : string) =
  let partner, action, label, payload, str = parseDotLabelPrefix str in
  let assertion, str = parseNewAssertionString str in
  let stateVars, str = parseRecVars str in
  let stateVars = List.map ~f:seqToString stateVars in
  if not (Sequence.is_empty str) then
    eprintf "Unexpected %s\n" (seqToString str) ;
  (partner, action, label, payload, assertion, stateVars)

let parseRecVarEntry (str : string) =
  let str = str |> String.to_list |> Sequence.of_list in
  let str = Sequence.drop_while ~f:(Char.( <> ) '<') str in
  match Sequence.hd str with
  | Some '<' ->
      let parseSingle str =
        let var, rest = span (Char.( <> ) ':') str in
        match Sequence.hd rest with
        | Some ':' -> (
            let rest = Sequence.tl_eagerly_exn rest in
            match Sequence.hd rest with
            | Some '=' ->
                let rest = Sequence.tl_eagerly_exn rest |> skipSpaces in
                (seqToString var, seqToString rest)
            | _ -> failwith "invalid initial expression, missing '='" )
        | _ -> failwith "invalid initial expression, missing ':'"
      in
      let rec aux str acc =
        let str = skipSpaces str in
        let expr, rest = span (fun c -> Char.(c <> '>' && c <> ',')) str in
        match Sequence.hd rest with
        | Some '>' ->
            let acc =
              if Sequence.is_empty expr then acc else parseSingle expr :: acc
            in
            let assertions =
              Sequence.tl_eagerly_exn rest
              |> skipSpaces |> seqToString |> fixAssertionDiscrepancy
            in
            (List.rev acc, assertions)
        | Some ',' ->
            aux (Sequence.tl_eagerly_exn rest) (parseSingle expr :: acc)
        | _ -> failwith "Unexpected recursion expression"
      in
      aux (Sequence.tl_eagerly_exn str) []
  | _ -> failwith "invalid recursion variable list, missing '<'"
