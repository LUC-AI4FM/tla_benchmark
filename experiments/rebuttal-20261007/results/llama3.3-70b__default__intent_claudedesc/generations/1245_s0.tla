```
MODULE CALToTLA
EXTENDS Integers, Sequences, TLC

CONSTANTS
  Algorithm,
  FairnessOption

VARIABLES
  ast,
  lexemes,
  pc,
  stack,
  vars,
  labels,
  actions,
  spec

Init ==
  /\ ast = Algorithm
  /\ lexemes = <<>>
  /\ pc = "start"
  /\ stack = <<>>
  /\ vars = {}
  /\ labels = {}
  /\ actions = {}
  /\ spec = FALSE

Next ==
  IF pc = "start" THEN
    /\ ast' = TranslateAlgorithm(ast, FairnessOption)
    /\ lexemes' = Append(lexemes, ast')
    /\ pc' = "done"
    /\ UNCHANGED <<stack, vars, labels, actions, spec>>
  ELSE
    /\ UNCHANGED <<ast, lexemes, pc, stack, vars, labels, actions, spec>>

TranslateAlgorithm(ast, fairness) ==
  CASE ast OF
    ("Uniprocess", alg) ->
      TranslateUniprocess(alg, fairness)
    ("Multiprocess", alg) ->
      TranslateMultiprocess(alg, fairness)
    ("Procedure", name, params, body) ->
      TranslateProcedure(name, params, body, fairness)
    ("Process", name, vars, body) ->
      TranslateProcess(name, vars, body, fairness)
    ("VariableDeclaration", var, type) ->
      TranslateVariableDeclaration(var, type)
    ("LabeledStatement", label, stmt) ->
      TranslateLabeledStatement(label, stmt, fairness)
    ("WhileLoop", cond, body) ->
      TranslateWhileLoop(cond, body, fairness)
    ("IfEitherWith", cond, thenBranch, elseBranch) ->
      TranslateIfEitherWith(cond, thenBranch, elseBranch, fairness)
    ("Call", procName, args) ->
      TranslateCall(procName, args, fairness)
    ("Return", value) ->
      TranslateReturn(value, fairness)
    ("CombinedCallReturn", procName, args, value) ->
      TranslateCombinedCallReturn(procName, args, value, fairness)
    ("Goto", label) ->
      TranslateGoto(label, fairness)
    ("Assignment", var, expr) ->
      TranslateAssignment(var, expr, fairness)
    ("When", cond, stmt) ->
      TranslateWhen(cond, stmt, fairness)
    ("Print", msg) ->
      TranslatePrint(msg, fairness)
    ("Assert", cond) ->
      TranslateAssert(cond, fairness)
    ("Skip", ) ->
      TranslateSkip(fairness)
  END

TranslateUniprocess(alg, fairness) ==
  LET vars == GetVariables(alg) IN
  LET labels == GetLabels(alg) IN
  LET actions == GetActions(alg, fairness) IN
  <<"/** Uniprocess Algorithm */",
    "/** Variables */",
    SequenceToLexemes(TranslateVariableDeclarations(vars)),
    "/** Labels */",
    SequenceToLexemes(labels),
    "/** Actions */",
    SequenceToLexemes(actions),
    "/** Next-state Action */",
    TranslateNextAction(alg, fairness),
    "/** Spec Formula */",
    TranslateSpecFormula(alg, fairness),
    "/** Termination Property */",
    TranslateTerminationProperty(alg, fairness)>>

TranslateMultiprocess(alg, fairness) ==
  LET procs == GetProcesses(alg) IN
  LET vars == GetVariables(alg) IN
  LET labels == GetLabels(alg) IN
  LET actions == GetActions(alg, fairness) IN
  <<"/** Multiprocess Algorithm */",
    "/** Variables */",
    SequenceToLexemes(TranslateVariableDeclarations(vars)),
    "/** Labels */",
    SequenceToLexemes(labels),
    "/** Actions */",
    SequenceToLexemes(actions),
    "/** Next-state Action */",
    TranslateNextAction(alg, fairness),
    "/** Spec Formula */",
    TranslateSpecFormula(alg, fairness),
    "/** Termination Property */",
    TranslateTerminationProperty(alg, fairness)>>

TranslateProcedure(name, params, body, fairness) ==
  <<"/** Procedure ", name, " */",
    "/** Parameters */",
    SequenceToLexemes(params),
    "/** Body */",
    TranslateAlgorithm(body, fairness)>>

TranslateProcess(name, vars, body, fairness) ==
  <<"/** Process ", name, " */",
    "/** Variables */",
    SequenceToLexemes(TranslateVariableDeclarations(vars)),
    "/** Body */",
    TranslateAlgorithm(body, fairness)>>

TranslateVariableDeclaration(var, type) ==
  <<var, " : ", type>>

TranslateLabeledStatement(label, stmt, fairness) ==
  <<label, " : ", TranslateAlgorithm(stmt, fairness)>>

TranslateWhileLoop(cond, body, fairness) ==
  <<"/** While Loop */",
    "/** Condition */",
    cond,
    "/** Body */",
    TranslateAlgorithm(body, fairness)>>

TranslateIfEitherWith(cond, thenBranch, elseBranch, fairness) ==
  <<"/** If Either With */",
    "/** Condition */",
    cond,
    "/** Then Branch */",
    TranslateAlgorithm(thenBranch, fairness),
    "/** Else Branch */",
    TranslateAlgorithm(elseBranch, fairness)>>

TranslateCall(procName, args, fairness) ==
  <<"/** Call ", procName, " */",
    "/** Arguments */",
    SequenceToLexemes(args)>>

TranslateReturn(value, fairness) ==
  <<"/** Return ", value>>

TranslateCombinedCallReturn(procName, args, value, fairness) ==
  <<"/** Combined Call Return ", procName, " */",
    "/** Arguments */",
    SequenceToLexemes(args),
    "/** Return Value */",
    value>>

TranslateGoto(label, fairness) ==
  <<"/** Goto ", label>>

TranslateAssignment(var, expr, fairness) ==
  <<var, " := ", expr>>

TranslateWhen(cond, stmt, fairness) ==
  <<"/** When ", cond, " */",
    "/** Statement */",
    TranslateAlgorithm(stmt, fairness)>>

TranslatePrint(msg, fairness) ==
  <<"/** Print ", msg>>

TranslateAssert(cond, fairness) ==
  <<"/** Assert ", cond>>

TranslateSkip(fairness) ==
  <<"/** Skip */">>

GetVariables(alg) ==
  CASE alg OF
    ("Uniprocess", vars) -> vars
    ("Multiprocess", procs) ->
      UNION {GetVariables(proc) : proc \in procs}
    ("Procedure", _, params, _) -> params
    ("Process", _, vars, _) -> vars
    _ -> {}
  END

GetLabels(alg) ==
  CASE alg OF
    ("Uniprocess", labels) -> labels
    ("Multiprocess", procs) ->
      UNION {GetLabels(proc) : proc \in procs}
    ("Procedure", _, _, body) -> GetLabels(body)
    ("Process", _, _, body) -> GetLabels(body)
    _ -> {}
  END

GetActions(alg, fairness) ==
  CASE alg OF
    ("Uniprocess", actions) ->
      IF fairness = "weak" THEN
        {action \in actions : action.type = "next"}
      ELSE
        actions
    ("Multiprocess", procs) ->
      UNION {GetActions(proc, fairness) : proc \in procs}
    ("Procedure", _, _, body) -> GetActions(body, fairness)
    ("Process", _, _, body) -> GetActions(body, fairness)
    _ -> {}
  END

TranslateNextAction(alg, fairness) ==
  CASE alg OF
    ("Uniprocess", next) ->
      IF fairness = "weak" THEN
        "/** Next-state Action */\n",
        SequenceToLexemes(next)
      ELSE
        "/** Next-state Action */\n",
        SequenceToLexemes(UNCHANGED <<next>>)
    ("Multiprocess", procs) ->
      LET nexts == {TranslateNextAction(proc, fairness) : proc \in procs} IN
      "/** Next-state Action */\n",
      SequenceToLexemes(Union(nexts))
    _ -> ""
  END

TranslateSpecFormula(alg, fairness) ==
  CASE alg OF
    ("Uniprocess", spec) ->
      IF fairness = "weak" THEN
        "/** Spec Formula */\n",
        spec
      ELSE
        "/** Spec Formula */\n",
        spec /\ [][Next]_vars
    ("Multiprocess", procs) ->
      LET specs == {TranslateSpecFormula(proc, fairness) : proc \in procs} IN
      "/** Spec Formula */\n",
      SequenceToLexemes(Intersection(specs))
    _ -> ""
  END

TranslateTerminationProperty(alg, fairness) ==
  CASE alg OF
    ("Uniprocess", term) ->
      IF fairness = "weak" THEN
        "/** Termination Property */\n",
        term
      ELSE
        "/** Termination Property */\n",
        term /\ [][Next]_vars
    ("Multiprocess", procs) ->
      LET terms == {TranslateTerminationProperty(proc, fairness) : proc \in procs} IN
      "/** Termination Property */\n",
      SequenceToLexemes(Intersection(terms))
    _ -> ""
  END

Spec ==
  /\ Init
  /\ [][Next]_ast
  /\ WF_vars(Next)

THEOREM Spec => []TerminationProperty
```