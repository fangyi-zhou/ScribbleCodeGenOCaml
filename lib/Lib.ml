let processScribbleOutput content protocol localRole recursiveRefinement =
  let parsed = DotParse.parse content in
  let cfsm = CFSMConversion.convert parsed recursiveRefinement in
  CodePrinter.generateCode cfsm protocol localRole
