open! Base
open Printf
open Types

type member = string

type field = string

type fieldType = string

type refinement = string

type tag = string

type unionCase = tag * fieldType list * refinement option

type recordItem = field * fieldType * refinement option

type typeDef = Union of unionCase list | Record of recordItem list

type content = typeDef smap

let defaultTypeAliasMap =
  Map.of_alist_exn
    (module String)
    [("_Unit", "unit"); ("int", "int"); ("string", "string")]

let resolveTypeAlias tyName =
  match Map.find defaultTypeAliasMap tyName with
  | Some ty -> ty
  | None -> tyName

let mkStateName state =
  let st = "state" in
  sprintf "%s%d" st state

let allRoles ((_, _, transitions, _) : cfsm) =
  let accumRoles ~key:_ ~data:transitions roles =
    let newRoles =
      List.map ~f:(fun (t : transition) -> t.partner) transitions
    in
    Set.union (Set.of_list (module String) newRoles) roles
  in
  Map.fold ~f:accumRoles ~init:(Set.empty (module String)) transitions

let allStates ((_, _, v, _) : cfsm) : state list =
  v |> Map.to_alist ~key_order:`Increasing |> List.map ~f:fst

let isDummy (x : string) = String.is_prefix x ~prefix:"_"

let convertAction action =
  match action with
  | Send -> "send"
  | Receive -> "receive"
  | Accept -> "accept"
  | Request -> "request"

let stateHasExternalChoice transitions =
  let receiveCount t =
    t |> List.filter ~f:(fun t -> Poly.(t.action = Receive)) |> List.length
  in
  receiveCount transitions > 1

let stateHasInternalChoice transitions =
  let receiveCount t =
    t |> List.filter ~f:(fun t -> Poly.(t.action = Send)) |> List.length
  in
  receiveCount transitions > 1

let productOfPayload payload =
  if List.is_empty payload then "unit"
  else
    let getType (_, tyName) = resolveTypeAlias tyName in
    List.map ~f:getType payload |> String.concat ~sep:" * "

let productOfRefinedPayload payload =
  if List.is_empty payload then "unit"
  else
    let getType (v, tyName, refinement) =
      match refinement with
      | Some r -> sprintf "%s:%s{%s}" v tyName r
      | None -> tyName
    in
    List.map ~f:getType payload |> String.concat ~sep:" * "

let curriedPayload payload =
  if List.is_empty payload then "unit"
  else
    let getType (_, tyName) = resolveTypeAlias tyName in
    List.map ~f:getType payload |> String.concat ~sep:" -> "

let curriedPayloadRefined payload =
  if List.is_empty payload then "unit"
  else
    let getType (var, tyName, refinement) =
      let refinement =
        match refinement with
        | Some r -> sprintf "%s{%s}" tyName r
        | None -> tyName
      in
      sprintf "(%s: %s)" var refinement
    in
    List.map ~f:getType payload |> String.concat ~sep:" -> "

let cleanUpVarMap stateVarMap =
  let cleanUpSingle (vars, assertions) =
    (List.filter ~f:(fun (name, _, _) -> not (isDummy name)) vars, assertions)
  in
  Map.map ~f:cleanUpSingle stateVarMap

let addRole content roles =
  let roleUnion =
    Union (Set.to_list roles |> List.map ~f:(fun role -> (role, [], None)))
  in
  Map.add_exn ~key:"Role" ~data:roleUnion content
