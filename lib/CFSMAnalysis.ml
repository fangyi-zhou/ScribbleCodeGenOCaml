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

let makeRefinementAttribute var ty terms codeGenMode =
  match terms with
  | [] -> None
  | terms -> (
      let terms = List.map ~f:termToString terms in
      let refinement = String.concat ~sep:" && " terms in
      match codeGenMode with
      | FStar -> Some refinement
      | _ -> Some (sprintf "{%s:%s|%s}" var ty refinement) )

let bindVars varsToBind binder term =
  let freeVars = FreeVar.free_var_term term in
  let varsToBind =
    Set.inter (Set.of_list (module String) varsToBind) freeVars
  in
  Set.fold
    ~f:(fun term var -> Substitution.substitute_term term var (binder var))
    ~init:term varsToBind

let attachRefinements refinements (vars, _) payloads binder codeGenMode =
  let addVariableWithRefinements (refinements, existingPayload) (var, ty) =
    let varsToBind = List.map ~f:fst vars in
    let knownVars = List.map ~f:(fun (v, _, _) -> v) existingPayload in
    let boundVars = Set.add (Set.of_list (module String) knownVars) var in
    let isRefinementClosed term =
      Set.is_subset (FreeVar.free_var_term term) ~of_:boundVars
    in
    let closed, notClosed =
      List.partition_tf ~f:isRefinementClosed refinements
    in
    let closed =
      match binder with
      | Some binder -> List.map ~f:(bindVars varsToBind binder) closed
      | None -> closed
    in
    let newPayloadItem =
      (var, ty, makeRefinementAttribute var ty closed codeGenMode)
    in
    ((notClosed, newPayloadItem :: existingPayload), newPayloadItem)
  in
  List.fold_map ~f:addVariableWithRefinements
    ~init:(refinements, List.map ~f:(fun (x, y) -> (x, y, None)) vars)
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
        | Some (recVar, recAssertion) ->
            (List.map ~f:(fun (v, _) -> (v, "int")) recVar, recAssertion)
        | None -> ([], [])
      in
      let vars = recVar @ vars in
      let assertions = recAssertion @ assertions in
      let varMap = Map.add_exn ~key:state ~data:(vars, assertions) varMap in
      let transitions = Map.find_exn allTransitions state in
      let updateWithTransition transition =
        let newAssertions = transition.assertion in
        let newVars = transition.payload in
        (vars @ newVars, assertions @ newAssertions)
      in
      List.fold
        ~f:(fun varMap transition ->
          aux varMap transition.toState (updateWithTransition transition))
        ~init:varMap transitions
  in
  aux (Map.empty (module Int)) init ([], [])
