let processScribbleOutput content protocol localRole codeGenMode
    recursiveRefinement =
  let parsed = DotParse.parse content in
  let cfsm = CFSMConversion.convert parsed recursiveRefinement in
  CodeGenCommon.codeGenMode := codeGenMode ;
  CodePrinter.generateCode cfsm protocol localRole
