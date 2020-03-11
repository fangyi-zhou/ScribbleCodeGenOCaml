open! Base
open Types
open CodeGenEventStyle

let generateCodeContent (cfsm : cfsm) stateVarMap localRole =
  generateCodeContentEventStyleApi cfsm stateVarMap localRole
