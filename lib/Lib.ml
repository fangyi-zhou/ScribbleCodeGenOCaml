let processScribbleOutput content protocol localRole =
  let parsed = DotParse.parse content in
  let cfsm = CFSMConversion.convert parsed in
  CodePrinter.generateCode cfsm protocol localRole
