open! Base
open Stdio
open Types

type attributes = string smap

type graphData = {nodes: attributes smap; edges: attributes list ssmap}

let newTransitionMap = Map.empty

let parse_term input =
  let lexbuf = Lexing.from_string input in
  ExprParser.expr ExprLexer.token lexbuf

let rec cutAssertion assertion =
  match assertion with
  | App (App (Const (Binop And), t1), t2) ->
      cutAssertion t1 @ cutAssertion t2
  | Const (BoolLiteral true) -> []
  | assertion -> [assertion]

let addTransition (transitions : transitionMap) (transition : transition) :
    transitionMap =
  let from = transition.fromState in
  Map.update transitions from ~f:(function
    | Some oldTransitions -> transition :: oldTransitions
    | None -> [transition])

let parseAssertionAndChunk assertion =
  if String.equal assertion "" then []
  else
    try
      let term = parse_term assertion in
      cutAssertion term
    with _ ->
      eprintf "Cannot parse %s, dropping\n" assertion ;
      []

let parseTransition fromState toState label : transition =
  let ( partner
      , action
      , label
      , irrpayload
      , payload
      , assertionString
      , recVarExpr ) =
    Parse.parseNewDotLabel label
  in
  let recVarExpr = List.map ~f:parse_term recVarExpr in
  { fromState
  ; toState
  ; partner
  ; action
  ; label= String.capitalize label
  ; irrpayload
  ; payload
  ; assertion= parseAssertionAndChunk assertionString
  ; recVarExpr }

let convertEdge ~key:((fromState, toState) : SS.t) ~(data : attributes list)
    (transitions : transitionMap) =
  (* printf "Adding (%s, %s)\n" fromState toState ; *)
  let attributes = data in
  let processAttribute transitions attribute =
    let fromState = Int.of_string fromState in
    let toState = Int.of_string toState in
    let label = Map.find_exn attribute "label" in
    let transition = parseTransition fromState toState label in
    addTransition transitions transition
  in
  List.fold ~f:processAttribute ~init:transitions attributes

let convertNode ~key ~(data : attributes) recVarMap =
  let state = key in
  let attributes = data in
  let state = Int.of_string state in
  let label = Map.find_exn attributes "label" in
  let recvars, irrrecvars, assertion = Parse.parseRecVarDef label in
  let assertion = parseAssertionAndChunk assertion in
  Map.add_exn ~key:state ~data:(irrrecvars, recvars, assertion) recVarMap

let convert (graph : graphData) : cfsm =
  let edges = graph.edges in
  let nodes = graph.nodes in
  let states =
    nodes
    |> Map.to_alist ~key_order:`Increasing
    |> List.map ~f:(fun (x, _) -> Int.of_string x)
  in
  let init = List.min_elt ~compare:Int.compare states in
  let init = Option.value_exn init in
  let recVarMap =
    Map.fold ~f:convertNode ~init:(Map.empty (module Int)) nodes
  in
  let initMap =
    List.map ~f:(fun state -> (state, [])) states
    |> Map.of_alist_exn (module Int)
  in
  let transitionMap = Map.fold ~f:convertEdge ~init:initMap edges in
  let finals =
    Map.filter ~f:(fun trans -> List.is_empty trans) transitionMap
    |> Map.to_alist ~key_order:`Increasing
    |> List.map ~f:fst
  in
  (init, finals, transitionMap, recVarMap)
