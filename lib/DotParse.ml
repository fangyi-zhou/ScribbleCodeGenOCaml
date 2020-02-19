open! Base
open CFSMConversion
open Graph
open Dot_ast

let unid = function Ident s | Number s | String s | Html s -> s

let unnode = function NodeId id -> unid (fst id) | _ -> assert false

let process_attr attrs =
  let f m (key, v_opt) =
    let key = unid key in
    let v_opt = Option.map ~f:unid v_opt in
    Map.add_exn m ~key ~data:(Option.value ~default:"" v_opt)
  in
  List.fold ~f ~init:(Map.empty (module String)) (List.concat attrs)

let parse content : graphData =
  let {stmts; _} = Dot.parse_dot_ast content in
  let f g = function
    | Node_stmt (nid, attr) ->
        let {nodes; _} = g in
        let attr = process_attr attr in
        let nodes = Map.add_exn nodes ~key:(unid (fst nid)) ~data:attr in
        {g with nodes}
    | Edge_stmt (nid1, nids, attr) ->
        let {edges; _} = g in
        let attr = process_attr attr in
        (* Only supporting one to-node *)
        let nid2 = List.hd_exn nids in
        let edges =
          Map.update edges
            (unnode nid1, unnode nid2)
            ~f:(fun o -> attr :: Option.value ~default:[] o)
        in
        {g with edges}
    | _ -> g
    (* | _ -> failwith "Not supported" *)
  in
  List.fold ~f
    ~init:
      {nodes= Map.empty (module String); edges= Map.empty (module Types.SS)}
    stmts
