---------------------------- MODULE XPlusCal ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Object, Any

VARIABLE ast, fairness

Translation(alg, fairnessOption) ==
  LET
    Explode(stmt) == 
      IF stmt \in LabeledStmt THEN
        FullyExplodeSeq(stmt.labelledStmts)
      ELSE << stmt >>
    FullyExplodeSeq(seq) == 
      Concatenate([Explode(stmt) | stmt <- seq])
    XlateCall(call) == 
      << "pc := ""call""", "stack := Append(stack, pc)" >>
    XlateReturn(ret) == 
      << "pc := ""return""", "stack := Tail(stack)" >>
    XlateCallReturn(cr) == 
      IF cr.type = "call" THEN XlateCall(cr)
      ELSE XlateReturn(cr)
    XlateGoto(goto) == 
      << "pc := ""goto""", "stack := Append(stack, pc)" >>
    AddSubscript(var, proc) == 
      var ++ "_" ++ proc
    ProcessVars(proc) == 
      {AddSubscript(var, proc) | var <- proc.vars}
    Init(alg) == 
      /\ pc = "init"
      /\ stack = << >>
      /\ [x \in ProcessVars(alg.procs) |-> NULL]
    Next(alg) == 
      /\ pc' = IF pc = "init" THEN "next" ELSE "same"
      /\ stack' = IF pc = "init" THEN << >> ELSE Append(stack, pc)
      /\ [x \in ProcessVars(alg.procs) |-> x']
    Spec(alg, fairnessOption) == 
      /\ Init(alg)
      /\ [][Next(alg)]
      /\ IF fairnessOption = "wf" THEN WF_vars(Next(alg))
      ELSE IF fairnessOption = "wfNext" THEN WF_vars(Next(alg)) \* [Next(alg)]_
      ELSE IF fairnessOption = "sf" THEN SF_vars(Next(alg))
  IN
    Concatenate([
      << "MODULE", alg.name >>
      , [<< "VARIABLE", var >> | var <- ProcessVars(alg.procs)]
      , [Translation(proc, fairnessOption) | proc <- alg.procs]
      , << "Init ==", Init(alg) >>
      , << "Next ==", Next(alg) >>
      , << "Spec ==", Spec(alg, fairnessOption) >>
    ])

ASSUME Translation(ast, fairness)
=============================================================================