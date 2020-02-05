open! Base
open Types

let special_this = "$this"

let rec free_var_term (term : term) : vset =
  match term with
  | Var v -> Set.singleton (module String) v
  | Const _ -> Set.empty (module String)
  | App (term_1, term_2) ->
      Set.union (free_var_term term_1) (free_var_term term_2)
  | Abs (v, term_) -> Set.remove (free_var_term term_) v
  | IfThenElse (term_cond, term_then, term_else) ->
      Set.union_list
        (module String)
        [ free_var_term term_cond
        ; free_var_term term_then
        ; free_var_term term_else ]
  | Anno (term_, ty) | Coerce (term_, ty) ->
      Set.union (free_var_term term_) (free_var_ty ty)
  | Let (var, t1, t2) ->
      Set.union (free_var_term t1) (Set.remove (free_var_term t2) var)
  | FieldGet (term_, _) -> free_var_term term_
  | NewRecord (terms, _) ->
      List.map ~f:free_var_term terms |> Set.union_list (module String)
  | UnknownTerm _ -> Set.empty (module String)
  | Tuple terms ->
      Set.union_list (module String) (List.map ~f:free_var_term terms)
  | Diverge -> Set.empty (module String)

and free_var_ty (ty : ty) : vset =
  match ty with
  | BaseType (_, term) -> Set.remove (free_var_term term) special_this
  | FuncType (v, t_arg, t_result) ->
      Set.union (free_var_ty t_arg) (Set.remove (free_var_ty t_result) v)
  | UnknownType _ -> Set.empty (module String)
  | RecordType _ -> Set.empty (module String)
  | UnionType _ -> Set.empty (module String)
  | ProductType tys ->
      Set.union_list (module String) (List.map ~f:free_var_ty tys)
