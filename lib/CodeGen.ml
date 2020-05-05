open! Base
open Types
open CodeGenEventStyle

let generateCodeContent (cfsm : cfsm) stateVarMap localRole customLabel =
  generateCodeContentEventStyleApi cfsm stateVarMap localRole customLabel
