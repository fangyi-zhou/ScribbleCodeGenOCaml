open! Base
open Types
open Printf

let find_replacement_var (v : variable) (excludes : vset) : variable =
  let rec aux i =
    let var = sprintf "%s_%d" v i in
    if Set.mem excludes var then aux (i + 1) else var
  in
  aux 0

let rec substitute_term (term : term) (x : variable) (replace : term) : term
    =
  let sub term = substitute_term term x replace in
  match term with
  | Var v when String.equal x v -> replace
  | Var _ -> term
  | Const _ -> term
  | Abs (v, _) when String.equal x v -> term
  | Abs (v, term_) ->
      let free_vars = FreeVar.free_var_term replace in
      if Set.mem free_vars v then
        sub (alpha_conv_term v (find_replacement_var v free_vars) term)
      else Abs (v, sub term_)
  | App (term_1, term_2) -> App (sub term_1, sub term_2)
  | IfThenElse (term_cond, term_then, term_else) ->
      IfThenElse (sub term_cond, sub term_then, sub term_else)
  | Anno (term_, ty) -> Anno (sub term_, substitute_ty ty x replace)
  | Coerce (term_, ty) -> Coerce (sub term_, substitute_ty ty x replace)
  | Let (v, t1, t2) ->
      let free_vars = FreeVar.free_var_term replace in
      if Set.mem free_vars v then
        sub (alpha_conv_term v (find_replacement_var v free_vars) term)
      else Let (v, sub t1, sub t2)
  | UnknownTerm _ -> term
  | FieldGet (term, field) -> FieldGet (sub term, field)
  | NewRecord (terms, record) -> NewRecord (List.map ~f:sub terms, record)
  | Tuple terms -> Tuple (List.map ~f:sub terms)
  | Diverge -> Diverge

and substitute_ty (ty : ty) (x : variable) (replace : term) : ty =
  let sub ty = substitute_ty ty x replace in
  match ty with
  | BaseType (basety, term) ->
      BaseType (basety, substitute_term term x replace)
  | FuncType (v, _, _) when String.equal x v -> ty
  | FuncType (v, t_arg, t_result) ->
      let free_vars = FreeVar.free_var_term replace in
      if Set.mem free_vars v then
        sub (alpha_conv_ty v (find_replacement_var v free_vars) ty)
      else FuncType (v, sub t_arg, sub t_result)
  | UnknownType _ -> ty
  | RecordType _ -> ty
  | UnionType _ -> ty
  | ProductType tys -> ProductType (List.map ~f:sub tys)

and alpha_conv_term (v_from : variable) (v_to : variable) (term : term) :
    term =
  (* Replace all bound `v_from` to `v_to` *)
  let conv term = alpha_conv_term v_from v_to term in
  match term with
  | Var v when String.equal v v_from -> Var v_to
  | Var v -> Var v
  | Const c -> Const c
  | Abs (v, term_) when String.equal v v_from ->
      Abs (v_to, substitute_term term_ v (Var v_to))
  | Abs (v, term_) -> Abs (v, conv term_)
  | App (term_1, term_2) -> App (conv term_1, conv term_2)
  | IfThenElse (term_cond, term_then, term_else) ->
      IfThenElse (conv term_cond, conv term_then, conv term_else)
  | Anno (term_, ty) -> Anno (conv term_, alpha_conv_ty v_from v_to ty)
  | Coerce (term_, ty) -> Coerce (conv term_, alpha_conv_ty v_from v_to ty)
  | Let (v, t1, t2) when String.equal v v_from ->
      Let (v_to, conv t1, substitute_term t2 v (Var v_to))
  | Let (v, t1, t2) -> Let (v, conv t1, conv t2)
  | FieldGet (term, field) -> FieldGet (conv term, field)
  | NewRecord (terms, record) -> NewRecord (List.map ~f:conv terms, record)
  | Tuple terms -> Tuple (List.map ~f:conv terms)
  | UnknownTerm (u, ty) -> UnknownTerm (u, ty)
  | Diverge -> Diverge

and alpha_conv_ty (v_from : variable) (v_to : variable) (ty : ty) : ty =
  (* Replace all bound `v_from` to `v_to` *)
  let conv ty = alpha_conv_ty v_from v_to ty in
  match ty with
  | BaseType (basety, term) ->
      BaseType (basety, alpha_conv_term v_from v_to term)
  | FuncType (v, t_arg, t_result) when String.equal v v_from ->
      let sub ty = substitute_ty ty v_from (Var v_to) in
      FuncType (v_to, sub t_arg, sub t_result)
  | FuncType (v, t_arg, t_result) -> FuncType (v, conv t_arg, conv t_result)
  | UnknownType _ -> ty
  | RecordType _ -> ty
  | UnionType _ -> ty
  | ProductType tys -> ProductType (List.map ~f:conv tys)
