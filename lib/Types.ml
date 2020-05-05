open! Base

type variable = string

type term =
  | Var of variable
  | Const of constant
  | App of term * term
  | Abs of variable * term
  | IfThenElse of term * term * term
  | Anno of term * ty
  | Coerce of term * ty
  | Let of variable * term * term
  | UnknownTerm of string * ty
  | NewRecord of term list * string
  | FieldGet of term * string
  | Tuple of term list
  | Diverge

and ty =
  | BaseType of basety * term
  | FuncType of variable * ty * (* of argument *) ty
  (* of result *)
  | UnknownType of string
  | RecordType of string
  | UnionType of string
  | ProductType of ty list

and basety = TBool | TInt

and constant =
  | IntLiteral of int
  | BoolLiteral of bool
  | Binop of binop
  | Unop of unop

and binop =
  | Plus
  | Minus
  | And
  | Or
  | EqualInt
  | NotEqualInt
  | EqualBool
  | NotEqualBool
  | Greater
  | GreaterEqual
  | Less
  | LessEqual

and unop = Not | Negate

type codeGenMode = FStar

type role = string

type label = string

type state = Int.t

type assertion = term list

type action = Request | Accept | Send | Receive

type vartype = string

type payloadItem = variable * vartype

type payload = payloadItem list

type transition =
  { fromState: state
  ; toState: state
  ; partner: role
  ; action: action
  ; label: label
  ; irrpayload: payload
  ; payload: payload
  ; assertion: assertion
  ; recVarExpr: term list }

type 'a stateMap = 'a Map.M(Int).t

type transitionMap = transition list stateMap

type recVarMap =
  (variable list * (variable * (* init expr *) string) list * assertion)
  stateMap

type cfsm =
  (* init *)
  state * (* terminal *) state list * transitionMap * recVarMap

type refinement = string

type stateVariableMap =
  ((variable * vartype * bool) list * assertion) stateMap

type vset = Set.M(String).t

type 'a seq = 'a Sequence.t

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
