open! Base
open Types
open CodeGenCommon
open CodeGenEventStyle

let generateCodeContent (cfsm : cfsm) stateVarMap localRole =
  match !codeGenMode with
  | FStar -> generateCodeContentEventStyleApi cfsm stateVarMap localRole
