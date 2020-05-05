open! Base
open! Stdio
open Printf
open Types
open Utils
open CodeGenCommon

let getCallbackType state transition =
  let action = transition.action in
  let payload =
    transition.payload |> List.filter ~f:(fun (x, _) -> not (isDummy x))
  in
  let argType =
    match action with
    | Send -> state
    | Receive -> curriedPayload (("state", state) :: payload)
    | _ -> failwith "TODO"
  in
  let retType =
    match action with
    | Send -> productOfPayload payload
    | Receive -> "unit"
    | _ -> failwith "TODO"
  in
  let eff = "ML " in
  sprintf "%s -> %s%s" argType eff retType

let getCallbackRefinement state varMap transition =
  let action = transition.action in
  let payload =
    transition.payload |> List.filter ~f:(fun (x, _) -> not (isDummy x))
  in
  let payload =
    if List.is_empty payload then [("_dummy", "unit")] else payload
  in
  let binder (v : variable) =
    App (Var (sprintf "Mk%s?.%s" state v), Var "st")
  in
  let _, payload =
    CFSMAnalysis.attachRefinements transition.assertion varMap payload
      (Some binder)
  in
  let argType =
    match action with
    | Send -> sprintf "(st: %s)" state
    | Receive -> curriedPayloadRefined (("st", state, None) :: payload)
    | _ -> failwith "TODO"
  in
  let retType =
    match action with
    | Send -> productOfRefinedPayload payload
    | Receive -> "unit"
    | _ -> failwith "TODO"
  in
  sprintf "%s -> ML (%s)" argType retType

let addSingleTransitionCallback stateVarMap callbacks transition =
  let action = convertAction transition.action in
  let fromState = transition.fromState in
  let label = transition.label in
  let field = sprintf "state%dOn%s%s" fromState action label in
  let state = mkStateName fromState in
  let _fieldType = getCallbackType state transition in
  let refinement =
    getCallbackRefinement state
      (Map.find_exn stateVarMap fromState)
      transition
  in
  (field, refinement, None) :: callbacks

let getChoiceRefinement state vars transition =
  let mkDisjunction cases =
    match cases with
    | [] -> mk_bool false
    | hd :: tl -> List.fold ~f:(mk_binop_app Or) ~init:hd tl
  in
  let mkConjunction cases =
    match cases with
    | [] -> mk_bool true
    | hd :: tl -> List.fold ~f:(mk_binop_app And) ~init:hd tl
  in
  let mkCase transition =
    let preconditions =
      List.filter
        ~f:(fun e -> Set.is_subset (FreeVar.free_var_term e) ~of_:vars)
        transition.assertion
    in
    let predicates =
      mk_binop_app EqualInt (Var "choice")
        (Var (sprintf "Choice%d%s" state transition.label))
      :: preconditions
    in
    mkConjunction predicates
  in
  let cases = List.map ~f:mkCase transition in
  let refinementTerm = mkDisjunction cases in
  let freeVars = FreeVar.free_var_term refinementTerm in
  let varsToBind = Set.inter vars freeVars in
  let binder (v : variable) =
    App (Var (sprintf "Mkstate%d?.%s" state v), Var "st")
  in
  let refinementTerm =
    Set.fold
      ~f:(fun term var -> Substitution.substitute_term term var (binder var))
      ~init:refinementTerm varsToBind
  in
  sprintf "(st: state%d) -> ML (choice:state%dChoice{%s})" state state
    (CFSMAnalysis.termToString refinementTerm)

let addSingleInternalChoiceSendCallback stateVarMap callbacks transition =
  (* TODO: Refactor *)
  let action = convertAction transition.action in
  let fromState = transition.fromState in
  let label = transition.label in
  let field = sprintf "state%dOn%s%s" fromState action label in
  let state = sprintf "%s_%s" (mkStateName fromState) transition.label in
  let _fieldType = getCallbackType state transition in
  (* TODO: Remove those refinements in predicate *)
  let refinement =
    getCallbackRefinement state
      (Map.find_exn stateVarMap fromState)
      transition
  in
  (field, refinement, None) :: callbacks

let addTransitionCallback stateVarMap ~key:state ~data:transition callbacks =
  if stateHasInternalChoice transition then
    let field = sprintf "state%dOnsend" state in
    (* let s = if Poly.(!codeGenMode = FStar) then 's' else 'S' in let eff =
       if Poly.(!codeGenMode = FStar) then "ML " else "" in let _fieldType =
       sprintf "%ctate%d -> %s%ctate%dChoice" s state eff s state in let
       currentStateVars = Map.find_exn stateVarMap state |> fst |> List.map
       ~f:fst |> Set.of_list (module String) in let refinement =
       getChoiceRefinement state currentStateVars transition in *)
    (* let callbacks = *)
    ( field
    , sprintf "(st: state%d) -> ML (state%dChoice st)" state state
    , None )
    :: callbacks
    (* nasty HACK *)
    (* in List.fold ~f:(addSingleInternalChoiceSendCallback stateVarMap)
       ~init:callbacks transition *)
  else
    List.fold
      ~f:(addSingleTransitionCallback stateVarMap)
      ~init:callbacks transition

let mkStateRecord (vars, assertions) =
  let fix_irr irrs closed =
    let f term =
      List.fold ~init:term
        ~f:(fun term irr ->
          Substitution.substitute_term term irr (App (Var "reveal", Var irr)))
        irrs
    in
    List.map ~f closed
  in
  let rec aux (vars, assertions, irrs) refinedPayload =
    match vars with
    | [] ->
        if
          not (List.is_empty assertions)
          (* then eprintf "Dropped assertions %A\n" assertions; *)
        then () ;
        List.rev refinedPayload
    | (var, ty, is_concrete) :: rest ->
        let knownVars = List.map ~f:(fun (v, _, _) -> v) refinedPayload in
        let boundVars =
          Set.add (Set.of_list (module String) knownVars) var
        in
        let isRefinementClosed term =
          Set.is_subset (FreeVar.free_var_term term) ~of_:boundVars
        in
        let closed, notClosed =
          List.partition_tf ~f:isRefinementClosed assertions
        in
        let newPayloadItem =
          let ty' = if is_concrete then ty else sprintf "erased %s" ty in
          let closed = fix_irr irrs closed in
          let refinement =
            CFSMAnalysis.makeRefinementAttribute var ty' closed
          in
          (var, ty', refinement)
        in
        let irrs = if is_concrete then irrs else var :: irrs in
        aux (rest, notClosed, irrs) (newPayloadItem :: refinedPayload)
  in
  Record (aux (vars, assertions, []) [])

let addStateRecords stateVarMap content =
  Map.fold
    ~f:(fun ~key:state ~data:stateVar content ->
      Map.add_exn ~key:(mkStateName state) ~data:(mkStateRecord stateVar)
        content)
    ~init:content stateVarMap

let addSendStatePredicate stateVarMap state content transition =
  let vars, assertions = Map.find_exn stateVarMap state in
  let currentStateVars =
    Map.find_exn stateVarMap state
    |> fst
    |> List.map ~f:(fun (x, _, _) -> x)
    |> Set.of_list (module String)
  in
  let preconditions =
    List.filter
      ~f:(fun e ->
        Set.is_subset (FreeVar.free_var_term e) ~of_:currentStateVars)
      transition.assertion
  in
  let record = mkStateRecord (vars, assertions @ preconditions) in
  let recordName = sprintf "state%d_%s" state transition.label in
  Map.add_exn ~key:recordName ~data:record content

let addInternalChoices stateVarMap ~key:state ~data:transition content =
  if stateHasInternalChoice transition then
    let choices =
      let f transition =
        let action = transition.action in
        let payload =
          transition.payload
          |> List.filter ~f:(fun (x, _) -> not (isDummy x))
        in
        let payload =
          if List.is_empty payload then [("_dummy", "unit")] else payload
        in
        let binder (v : variable) =
          App (Var (sprintf "Mkstate%d?.%s" state v), Var "st")
        in
        let varMap = Map.find_exn stateVarMap state in
        let _, payload =
          CFSMAnalysis.attachRefinements transition.assertion varMap payload
            (Some binder)
        in
        let retType =
          match action with
          | Send -> productOfRefinedPayload payload
          | Receive -> "unit"
          | _ -> failwith "TODO"
        in
        (sprintf "Choice%d%s" state transition.label, [retType], None)
      in
      List.map ~f transition
    in
    let union = Union choices in
    Map.add_exn
      ~key:(sprintf "state%dChoice (st: state%d)" state state)
      ~data:union content
    (* in List.fold ~f:(addSendStatePredicate stateVarMap state)
       ~init:content transition *)
  else content

let getLabels transitions =
  let f ~key:_ ~data acc =
    let f acc transition = Set.add acc transition.label in
    List.fold ~f ~init:acc data
  in
  let labels = Map.fold ~f ~init:(Set.empty (module String)) transitions in
  let labels =
    Union (List.map ~f:(fun ctor -> (ctor, [], None)) (Set.to_list labels))
  in
  Map.singleton (module String) "label" labels

let generateCodeContentEventStyleApi cfsm stateVarMap localRole customLabel =
  let _, _, transitions, _ = cfsm in
  let states = allStates cfsm in
  let roles = allRoles cfsm in
  assert (List.length states = Map.length stateVarMap) ;
  let stateRecords =
    addStateRecords stateVarMap (Map.empty (module String))
  in
  let roles = addRole (Map.empty (module String)) roles in
  let choices =
    Map.fold
      ~f:(addInternalChoices stateVarMap)
      ~init:(Map.empty (module String))
      transitions
  in
  let callbacks =
    Map.fold ~f:(addTransitionCallback stateVarMap) ~init:[] transitions
    |> List.rev
  in
  let callbacks =
    Map.of_alist_exn
      (module String)
      [("Callbacks" ^ localRole, Record callbacks)]
  in
  if customLabel then
    let labels = getLabels transitions in
    [roles; labels; stateRecords; choices; callbacks]
  else [roles; stateRecords; choices; callbacks]
