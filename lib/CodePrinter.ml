open! Base
open! Stdio
open Caml.Format
open Types
open CodeGenCommon
open CodeGen
open Printf

let moduleName = ref "ScribbleGenerated"

let fileName = ref "ScribbleGenerated.fs"

(*TODO*)
let indent _ = ()

(*TODO*)
let unindent _ = ()

let writeln fmt (str : string) =
  pp_print_string fmt str ; pp_print_newline fmt ()

let ensureStartsWithLowerCase (string : string) = String.uncapitalize string

let writeTypeDefPreamble writer isFirst (name : string) content =
  let noeq =
    if
      String.is_prefix name ~prefix:"Callbacks"
      || String.is_prefix name ~prefix:"state"
    then "noeq "
    else ""
    (* Yet another nasty HACK *)
  in
  let preamble = if isFirst then noeq ^ "type" else "and" in
  let name = ensureStartsWithLowerCase name in
  fprintf writer "%s %s%s\n" preamble name content

let writeUnionCase writer (tag, fieldTypes, refinement) =
  let refinement =
    match refinement with
    | Some r -> sprintf "[<Refined(\"%s\")>] " r
    | None -> ""
  in
  let fields =
    match fieldTypes with
    | [] -> ""
    | fields -> sprintf " of %s" (String.concat ~sep:" * " fields)
  in
  fprintf writer "| %s%s%s\n" tag refinement fields

let writeUnion writer isFirst name union =
  writeTypeDefPreamble writer isFirst name " =" ;
  indent writer ;
  List.iter ~f:(writeUnionCase writer) union ;
  unindent writer

let writeRecordItem writer (field, fieldType, refinement) =
  let isErased = String.is_prefix fieldType ~prefix:"erased " in
  let refinedType =
    if isErased then
      let ty = String.chop_prefix_exn fieldType ~prefix:"erased " in
      match refinement with
      | Some refinement -> sprintf "erased (%s : %s{%s})" field ty refinement
      | None -> fieldType
    else
      match refinement with
      | Some refinement -> sprintf "(%s : %s{%s})" field fieldType refinement
      | None -> fieldType
  in
  fprintf writer "%s : %s;\n" field refinedType

let writeRecord writer isFirst name record =
  if List.is_empty record then
    (* F# doesn't allow empty record *)
    writeTypeDefPreamble writer isFirst name " = unit"
  else (
    writeTypeDefPreamble writer isFirst name " = {" ;
    indent writer ;
    (* FIXME: Hack *)
    if String.is_prefix name ~prefix:"state" then
      fprintf writer "_dum%s : unit;\n" name ;
    List.iter ~f:(writeRecordItem writer) record ;
    unindent writer ;
    writeln writer "}" )

let writeTypeDef writer isFirst (name, typeDef) =
  match typeDef with
  | Union u -> writeUnion writer isFirst name u
  | Record r -> writeRecord writer isFirst name r

let writeContents writer (content : content) =
  let content = Map.to_alist ~key_order:`Increasing content in
  match content with
  | [] -> ()
  | first :: rest ->
      writeTypeDef writer true first ;
      List.iter ~f:(writeTypeDef writer false) rest

let generatePreamble writer _moduleName _protocol _localRole =
  let moduleName = Caml.Filename.remove_extension !fileName in
  fprintf writer "module %s\n" moduleName ;
  writeln writer "(* This file is GENERATED, do not modify manually *)" ;
  (* if Poly.(!codeGenMode <> FStar) then writeln writer "open
     FluidTypes.Annotations" *)
  writeln writer "open FStar.All" ;
  writeln writer "open FStar.Ghost" ;
  writeln writer "open FStar.Error" ;
  writeln writer ""

(* //writeln writer ("let send_int : int -> unit = failwith \"TODO\"")
   //writeln writer ("let send_string : string -> unit = failwith \"TODO\"")
   //writeln writer ("let send_unit : unit -> unit = failwith \"TODO\"")
   //writeln writer ("let recv_int : unit -> int = failwith \"TODO\"")
   //writeln writer ("let recv_string : unit -> string = failwith \"TODO\"")
   //writeln writer ("let recv_unit : unit -> unit = failwith \"TODO\"")
   //writeln writer "" *)

let assembleState writer (stateVarMap : stateVariableMap) recVarMap state var
    stateTy prevStateTy recExprs =
  let fieldGet field stateName = sprintf "(Mk%s?.%s st)" stateName field in
  let recExprs = Map.of_alist_exn (module String) recExprs in
  let getInitExpr v =
    match Map.find recVarMap state with
    | Some (_, vars, _) ->
        let vars = Map.of_alist_exn (module String) vars in
        Map.find vars v
    | None -> None
  in
  let vars =
    Map.find_exn stateVarMap state
    |> fst
    |> List.map ~f:(fun (x, _, is_concrete) -> (x, is_concrete))
  in
  if List.is_empty vars then fprintf writer "()\n"
  else (
    fprintf writer "{\n" ;
    indent writer ;
    fprintf writer "_dum%s = ();\n" stateTy ;
    let getVar v is_concrete =
      match v with
      | v when String.equal v var -> v
      | v when Map.mem recExprs v -> Map.find_exn recExprs v
      | _v when not is_concrete -> "(assume false; hide 0)"
      | v -> Option.value ~default:(fieldGet v prevStateTy) (getInitExpr v)
    in
    List.iter
      ~f:(fun (v, is_concrete) ->
        fprintf writer "%s = %s;\n" v (getVar v is_concrete))
      vars ;
    unindent writer ;
    fprintf writer "}\n" )

let generateRunState writer (cfsm : cfsm) stateVarMap customLabel isInit
    state =
  let in_ = " in" in
  let in__ writer = writeln writer "in" in
  let semi_ = ";" in
  (* let bang = if Poly.(!codeGenMode = EventApi) then "!" else "" in let
     doBang = if Poly.(!codeGenMode = EventApi) then "do! " else "" in let
     returnBang = if Poly.(!codeGenMode = EventApi) then "return! " else ""
     in *)
  let bang = "" in
  let doBang = "" in
  let returnBang = "" in
  let stateTy = "state" in
  let _, finalStates, transitions, recVarMap = cfsm in
  let functionName = sprintf "runState%d" state in
  let preamble = if isInit then "let rec" else "and" in
  let () =
    fprintf writer "%s %s (st: %s%d) : ML unit =\n" preamble functionName
      stateTy state
  in
  indent writer ;
  (* let () = if Poly.(!codeGenMode = EventApi) then writeln writer "async {"
     ; indent writer in *)
  let generateForTransition t prevStateName =
    match t with
    | { action= a
      ; payload= p
      ; label= l
      ; toState
      ; partner= r
      ; recVarExpr= recExprs
      ; _ } ->
        let p = if List.is_empty p then [("_dummy", "unit")] else p in
        if List.length p = 1 then (
          let var, ty = List.hd_exn p in
          let ty = resolveTypeAlias ty in
          let () =
            match a with
            | Send ->
                let () =
                  if customLabel then
                    fprintf writer "%scomms.send_label %s %s%s\n" doBang r l
                      semi_
                  else
                    fprintf writer "%scomms.send_string %s \"%s\"%s\n" doBang
                      r l semi_
                in
                let callbackName = sprintf "state%dOnsend%s" state l in
                fprintf writer "let %s = callbacks.%s st%s\n" var
                  callbackName in_ ;
                fprintf writer "%scomms.send_%s %s %s%s\n" doBang ty r var
                  semi_
            | Receive ->
                (* //writeln writer "let label = recv_string ()" //writeln
                   writer "assert (label = \"%s\")" l *)
                let callbackName = sprintf "state%dOnreceive%s" state l in
                fprintf writer "let%s %s = comms.recv_%s %s ()%s\n" bang var
                  ty r in_ ;
                let () =
                  let binder (v : variable) =
                    App (Var (sprintf "Mkstate%d?.%s" state v), Var "st")
                  in
                  let varMap = Map.find_exn stateVarMap state in
                  let _, payload =
                    CFSMAnalysis.attachRefinements t.assertion varMap p
                      (Some binder)
                  in
                  match payload with
                  | [(_, _, Some r)] -> fprintf writer "assume (%s);\n" r
                  | [(_, _, None)] -> ()
                  | _ -> failwith "Unreachable"
                in
                fprintf writer "callbacks.%s st %s%s\n" callbackName
                  (if isDummy var then "()" else var)
                  semi_
            | _ -> failwith "TODO"
          in
          let stateTyName = sprintf "%s%d" stateTy toState in
          fprintf writer "let st : %s = " stateTyName ;
          let prevStateName =
            Option.value ~default:(sprintf "state%d" state) prevStateName
          in
          let recVars =
            Map.find recVarMap toState
            |> Option.map ~f:(fun (_, x, _) -> List.map ~f:fst x)
            |> Option.value ~default:[]
          in
          let bindVar v =
            if String.equal v var then Var var
            else App (Var (sprintf "Mkstate%d?.%s" state v), Var "st")
          in
          let stateVars =
            Map.find_exn stateVarMap state
            |> fst
            |> List.map ~f:(fun (x, _, _) -> x)
          in
          let recExprs =
            List.map
              ~f:(fun v ->
                v
                |> CFSMAnalysis.bindVars stateVars bindVar
                |> CFSMAnalysis.termToString)
              recExprs
          in
          assembleState writer stateVarMap recVarMap toState var stateTyName
            prevStateName
            (List.zip_exn recVars recExprs) ;
          in__ writer ;
          fprintf writer "%srunState%d st\n" returnBang toState )
        else failwith "Currently only support single payload"
  in
  let () =
    if List.mem finalStates state ~equal:Int.equal then writeln writer "()"
    else
      let stateTransition = Map.find_exn transitions state in
      if
        List.length stateTransition = 1
        && Poly.((List.hd_exn stateTransition).action = Send)
      then
        (* Singleton send *)
        generateForTransition (List.hd_exn stateTransition) None
      else
        (* Branch and Select *)
        match List.hd_exn stateTransition with
        (* From Scribble, we know that the action of all outgoing transitions
           must be the same *)
        | {action= Send; _} ->
            let generateCase transition =
              let label = transition.label in
              let p = transition.payload in
              let p = if List.is_empty p then [("_dummy", "unit")] else p in
              let var, ty = List.hd_exn p in
              let ty = resolveTypeAlias ty in
              let r = transition.partner in
              let l = transition.label in
              let toState = transition.toState in
              let recExprs = transition.recVarExpr in
              (* let () = if Poly.(!codeGenMode = FStar) then *)
              fprintf writer "| Choice%d%s %s ->\n" state label var ;
              (* else fprintf writer "| State%dChoice.%s ->\n" state label in *)
              let () =
                if customLabel then
                  fprintf writer "%scomms.send_label %s %s%s\n" doBang r l
                    semi_
                else
                  fprintf writer "%scomms.send_string %s \"%s\"%s\n" doBang r
                    l semi_
              in
              fprintf writer "%scomms.send_%s %s %s%s\n" doBang ty r var
                semi_ ;
              let stateTyName = sprintf "%s%d" stateTy toState in
              fprintf writer "let st : %s = " stateTyName ;
              let prevStateName = sprintf "state%d" state in
              let recVars =
                Map.find recVarMap toState
                |> Option.map ~f:(fun (_, x, _) -> List.map ~f:fst x)
                |> Option.value ~default:[]
              in
              let bindVar v =
                if String.equal v var then Var var
                else App (Var (sprintf "Mkstate%d?.%s" state v), Var "st")
              in
              let stateVars =
                Map.find_exn stateVarMap state
                |> fst
                |> List.map ~f:(fun (x, _, _) -> x)
              in
              let recExprs =
                List.map
                  ~f:(fun v ->
                    v
                    |> CFSMAnalysis.bindVars stateVars bindVar
                    |> CFSMAnalysis.termToString)
                  recExprs
              in
              assembleState writer stateVarMap recVarMap toState var
                stateTyName prevStateName
                (List.zip_exn recVars recExprs) ;
              in__ writer ;
              fprintf writer "%srunState%d st\n" returnBang toState
            in
            fprintf writer "let label = callbacks.state%dOnsend st%s\n" state
              in_ ;
            fprintf writer "match label with\n" ;
            indent writer ;
            List.iter ~f:generateCase stateTransition ;
            unindent writer
        | {action= Receive; partner= role; _} ->
            let generateCase transition =
              let label = transition.label in
              let () =
                if customLabel then fprintf writer "| %s ->\n" label
                else fprintf writer "| \"%s\" ->\n" label
              in
              indent writer ;
              generateForTransition transition None ;
              unindent writer
            in
            let () =
              if customLabel then
                fprintf writer "let%s label = comms.recv_label %s ()%s\n"
                  bang role in_
              else
                fprintf writer "let%s label = comms.recv_string %s ()%s\n"
                  bang role in_
            in
            fprintf writer "match label with\n" ;
            indent writer ;
            List.iter ~f:generateCase stateTransition ;
            let fail = "unexpected" in
            fprintf writer "| _ -> %s \"unexpected label\"\n" fail ;
            unindent writer
        | _ -> failwith "TODO"
  in
  (* if Poly.(!codeGenMode = EventApi) then ( unindent writer ; fprintf
     writer "}\n" ) ; *)
  unindent writer ; false

let generateRuntimeCode writer (cfsm : cfsm) stateVarMap customLabel =
  let initState, _, _, recVarMap = cfsm in
  let states = allStates cfsm in
  let in__ writer = writeln writer "in" in
  let stateTy = "state" in
  let stateName = sprintf "%s%d" stateTy initState in
  indent writer ;
  (* printfn "%A" cfsm *)
  List.fold
    ~f:(generateRunState writer cfsm stateVarMap customLabel)
    ~init:true states
  |> ignore ;
  in__ writer ;
  fprintf writer "let initState : %s =\n" stateName ;
  indent writer ;
  assembleState writer stateVarMap recVarMap initState "" stateName "" [] ;
  unindent writer ;
  in__ writer ;
  fprintf writer "runState%d initState\n" initState ;
  unindent writer

let writeCommunicationDef writer customLabel =
  let noeq = "noeq " in
  let comm = "connection" in
  let role = "role" in
  let mkReturn ty = sprintf "ML %s" ty in
  let mkSend name =
    sprintf "send_%s : %s -> %s -> %s;\n" name role name (mkReturn "unit")
  in
  let mkRecv name =
    sprintf "recv_%s : %s -> %s -> %s;\n" name role "unit" (mkReturn name)
  in
  let types =
    if customLabel then ["int"; "string"; "unit"; "label"]
    else ["int"; "string"; "unit"]
  in
  fprintf writer "%stype %s = {\n" noeq comm ;
  List.iter
    ~f:(fun ty -> fprintf writer "%s%s" (mkSend ty) (mkRecv ty))
    types ;
  fprintf writer "}\n"

let generateCode (cfsm : cfsm) protocol localRole customLabel =
  let file = Out_channel.create !fileName in
  let writer = Caml.Format.formatter_of_out_channel file in
  let stateVarMap = CFSMAnalysis.constructVariableMap cfsm in
  let stateVarMap = cleanUpVarMap stateVarMap in
  generatePreamble writer !moduleName protocol localRole ;
  let content = generateCodeContent cfsm stateVarMap localRole customLabel in
  List.iter ~f:(writeContents writer) content ;
  writeCommunicationDef writer customLabel ;
  let () =
    fprintf writer
      "let run (callbacks : callbacks%s) (comms : connection) : ML unit =\n"
      localRole ;
    generateRuntimeCode writer cfsm stateVarMap customLabel
  in
  Caml.Format.pp_print_flush writer () ;
  Out_channel.close file
