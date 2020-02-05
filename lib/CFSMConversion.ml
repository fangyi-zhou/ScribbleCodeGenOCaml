open! Base
open Stdio
open Types

module SS = struct
  module M = struct
    type t = string * string

    let compare (s11, s12) (s21, s22) =
      let cmp1 = String.compare s11 s21 in
      if cmp1 = 0 then String.compare s12 s22 else cmp1

    let sexp_of_t (s1, s2) = sexp_of_list sexp_of_string [s1; s2]
  end

  include M
  include Comparator.Make (M)
end

type 'a smap = 'a Map.M(String).t

type 'a ssmap = 'a Map.M(SS).t

type attributes = string smap

type graphData =
  { nodes: attributes smap
  ; edges: attributes list ssmap
  ; graphAttributes: attributes
  ; nodeAttributes: attributes
  ; edgeAttributes: attributes }

let newSyntax = ref false

let newTransitionMap = Map.empty

let parse_term _ = assert false

let rec cutAssertion assertion =
  match assertion with
  | App (App (Const (Binop And), t1), t2) ->
      cutAssertion t1 @ cutAssertion t2
  | Const (BoolLiteral true) -> []
  | assertion -> [assertion]

let addTransition (transitions : transitionMap) (transition : transition) :
    transitionMap =
  let from = transition.fromState in
  match Map.find transitions from with
  | Some oldTransitions ->
      Map.add_exn transitions ~key:from ~data:(transition :: oldTransitions)
  | None -> Map.add_exn transitions ~key:from ~data:[transition]

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
  let partner, action, label, payload, assertionString, recVarExpr =
    if not !newSyntax then Parse.parseOldDotLabel label
    else Parse.parseNewDotLabel label
  in
  let recVarExpr = List.map ~f:parse_term recVarExpr in
  { fromState
  ; toState
  ; partner
  ; action
  ; label
  ; payload
  ; assertion= parseAssertionAndChunk assertionString
  ; recVarExpr }

let convertEdge ~key:((fromState, toState) : SS.t) ~(data : attributes list)
    (transitions : transitionMap) =
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
  if not !newSyntax then recVarMap
  else
    let state = Int.of_string state in
    let label = Map.find_exn attributes "label" in
    let recvars, assertion = Parse.parseRecVarEntry label in
    let assertion = parseAssertionAndChunk assertion in
    Map.add_exn ~key:state ~data:(recvars, assertion) recVarMap

let convert (graph : graphData) (recursiveRefinement : bool) : cfsm =
  newSyntax := recursiveRefinement ;
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
