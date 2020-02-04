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
  | Unknownterm of string * ty
  | NewRecord of term list * string
  | FieldGet of term * string
  | Tuple of term list
  | Diverge

and ty =
  | Basetype of basety * term
  | Functype of variable * ty * (* of argument *) ty
  (* of result *)
  | Unknowntype of string
  | Recordtype of string
  | Uniontype of string
  | Producttype of ty list

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

type codeGenMode = LegacyApi | EventApi | FStar

type role = string

type label = string

type state = int

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
  ; payload: payload
  ; assertion: assertion
  ; recVarExpr: term list }

type 'a stateMap = 'a Map.M(Int).t

type transitionMap = transition list stateMap

type recVarMap =
  ((variable * (* init expr *) string) list * assertion) stateMap

type cfsm =
  (* init *)
  state * (* terminal *) state list * transitionMap * recVarMap

type refinement = string

type stateVariableMap = ((variable * vartype) list * assertion) stateMap
