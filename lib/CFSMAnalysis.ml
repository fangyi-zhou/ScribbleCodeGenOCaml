open! Base
open Types
open Printf

(* I know this should not be here, but whatever *)
let rec termToString term =
  match term with
  | Var v -> sprintf "(%s)" v
  | Const (IntLiteral i) -> sprintf "(%d)" i
  | Const (BoolLiteral b) -> if b then "(true)" else "(false)"
  | App (App (Const (Binop b), t1), t2) ->
      sprintf "(%s %s %s)" (termToString t1) (binopToString b)
        (termToString t2)
  | App (Const (Unop u), t1) ->
      sprintf "(%s %s)" (unopToString u) (termToString t1)
  | App (Var v1, Var v2) -> sprintf "(%s %s)" v1 v2
  | App (Var "reveal", t) -> sprintf "reveal (%s)" (termToString t)
  | FieldGet (t, v) -> sprintf "(%s$%s)" (termToString t) v
  | _ -> failwith "TODO"

and binopToString b =
  match b with
  | Plus -> "+"
  | Minus -> "-"
  | EqualInt | EqualBool -> "="
  | NotEqualInt | NotEqualBool -> "<>"
  | And -> "&&"
  | Or -> "||"
  | Greater -> ">"
  | GreaterEqual -> ">="
  | Less -> "<"
  | LessEqual -> "<="

and unopToString u = match u with Negate -> "-" | Not -> "not"

let makeRefinementAttribute _ _ terms =
  match terms with
  | [] -> None
  | terms ->
      let terms = List.map ~f:termToString terms in
      let refinement = String.concat ~sep:" && " terms in
      Some refinement

let bindVars varsToBind binder term =
  let freeVars = FreeVar.free_var_term term in
  let varsToBind =
    Set.inter (Set.of_list (module String) varsToBind) freeVars
  in
  Set.fold
    ~f:(fun term var -> Substitution.substitute_term term var (binder var))
    ~init:term varsToBind

let attachRefinements refinements (vars, _) payloads binder =
  let addVariableWithRefinements (refinements, existingPayload) (var, ty) =
    let is_irrelevant v =
      List.exists
        ~f:(fun (x, _, is_concrete) -> String.equal x v && not is_concrete)
        vars
    in
    let varsToBind = List.map ~f:(fun (x, _, _) -> x) vars in
    let knownVars = List.map ~f:(fun (v, _, _) -> v) existingPayload in
    let boundVars = Set.add (Set.of_list (module String) knownVars) var in
    let isRefinementClosed term =
      Set.is_subset (FreeVar.free_var_term term) ~of_:boundVars
    in
    let closed, notClosed =
      List.partition_tf ~f:isRefinementClosed refinements
    in
    let closed =
      let binder = Option.value binder ~default:(fun x -> Var x) in
      let binder v =
        let bound = binder v in
        if is_irrelevant v then App (Var "reveal", bound) else bound
      in
      List.map ~f:(bindVars varsToBind binder) closed
    in
    let newPayloadItem = (var, ty, makeRefinementAttribute var ty closed) in
    ((notClosed, newPayloadItem :: existingPayload), newPayloadItem)
  in
  List.fold_map ~f:addVariableWithRefinements
    ~init:(refinements, List.map ~f:(fun (x, y, _) -> (x, y, None)) vars)
    payloads

let constructVariableMap (cfsm : cfsm) : stateVariableMap =
  let init, finals, allTransitions, recVars = cfsm in
  let rec aux (varMap : stateVariableMap) (state : state) (vars, assertions)
      =
    if Map.mem varMap state then varMap
    else if List.mem ~equal:Int.equal finals state then
      Map.add_exn ~key:state ~data:([], []) varMap
    else
      let recVar, recAssertion =
        match Map.find recVars state with
        | Some (irrrecVar, recVar, recAssertion) ->
            ( List.map ~f:(fun (v, _) -> (v, "int", true)) recVar
              @ List.map ~f:(fun v -> (v, "int", false)) irrrecVar
            , recAssertion )
        | None -> ([], [])
      in
      let vars = recVar @ vars in
      let assertions = recAssertion @ assertions in
      let varMap = Map.add_exn ~key:state ~data:(vars, assertions) varMap in
      let transitions = Map.find_exn allTransitions state in
      let updateWithTransition transition =
        let newAssertions = transition.assertion in
        let newVars =
          List.map ~f:(fun (x, y) -> (x, y, true)) transition.payload
        in
        let newIrrVars =
          List.map ~f:(fun (x, y) -> (x, y, false)) transition.irrpayload
        in
        (vars @ newVars @ newIrrVars, assertions @ newAssertions)
      in
      List.fold
        ~f:(fun varMap transition ->
          aux varMap transition.toState (updateWithTransition transition))
        ~init:varMap transitions
  in
  aux (Map.empty (module Int)) init ([], [])
