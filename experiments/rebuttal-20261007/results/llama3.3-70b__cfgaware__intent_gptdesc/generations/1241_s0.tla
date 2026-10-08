---------------------------- MODULE Translator ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Object, Any

VARIABLES program, targetSpec, callStack, processTable

TypeOK == /\ program \in [Any -> Any]
           /\ targetSpec \in [Any -> Any]

Init ==
  /\ program = << >>
  /\ targetSpec = << >>
  /\ callStack = << >>
  /\ processTable = << >>

TranslateProgram ==
  /\ program' = program
  /\ targetSpec' = Translate(program)
  /\ callStack' = << >>
  /\ processTable' = << >>

Translate(p) ==
  CASE p OF
    ("Procedure" => procName, params, body) =>
      /\ targetSpec' = [targetSpec EXCEPT ![procName] = TranslateProc(body, params)]
      /\ callStack' = << >>
      /\ processTable' = << >>
    ("Assignment" => var, expr) =>
      /\ targetSpec' = [targetSpec EXCEPT ![var] = Evaluate(expr)]
      /\ callStack' = << >>
      /\ processTable' = << >>
    ("Conditional" => cond, thenBranch, elseBranch) =>
      /\ targetSpec' = [targetSpec EXCEPT !["if"] = Translate(cond), !"then" = Translate(thenBranch), !"else" = Translate(elseBranch)]
      /\ callStack' = << >>
      /\ processTable' = << >>
    ("Loop" => loopBody) =>
      /\ targetSpec' = [targetSpec EXCEPT ![loopBody] = Translate(loopBody)]
      /\ callStack' = << >>
      /\ processTable' = << >>
    ("ProcedureCall" => procName, args) =>
      /\ targetSpec' = [targetSpec EXCEPT ![procName] = TranslateProcCall(procName, args)]
      /\ callStack' = << procName >> \o callStack
      /\ processTable' = << >>
    ("Return" => ) =>
      /\ targetSpec' = [targetSpec EXCEPT !["return"] = TRUE]
      /\ callStack' = Tail(callStack)
      /\ processTable' = << >>
  END

TranslateProc(body, params) ==
  /\ procBody = Translate(body)
  /\ procParams = params
  /\ procSpec = [procBody EXCEPT ![params] = procParams]

TranslateProcCall(procName, args) ==
  /\ procSpec = targetSpec[procName]
  /\ procArgs = args
  /\ callSpec = [procSpec EXCEPT ![args] = procArgs]

Evaluate(expr) ==
  CASE expr OF
    ("Constant" => value) => value
    ("Variable" => var) => program[var]
    ("Operation" => op, args) => ApplyOp(op, args)
  END

ApplyOp(op, args) ==
  CASE op OF
    "+" => Plus(args[1], args[2])
    "-" => Minus(args[1], args[2])
    "*" => Times(args[1], args[2])
    "/" => Divide(args[1], args[2])
  END

Plus(a, b) == a + b
Minus(a, b) == a - b
Times(a, b) == a * b
Divide(a, b) == IF b = 0 THEN undefined ELSE a / b

SemanticPreservation ==
  /\ \A p \in program : \E ts \in targetSpec : ts = Translate(p)
  /\ \A ts \in targetSpec : \E p \in program : ts = Translate(p)

SafetyProperties ==
  /\ \A inv \in program : inv \in targetSpec
  /\ \A assert \in program : assert \in targetSpec

TerminationPreservation ==
  /\ \A term \in program : term \in targetSpec

ErrorHandling ==
  /\ \A p \in program :
      IF IsDuplicateDecl(p) THEN targetSpec = undefined
      ELSEIF IsNonConstantInitializer(p) THEN targetSpec = undefined
      ELSEIF IsIllegalLocalName(p) THEN targetSpec = undefined
      ELSE targetSpec = Translate(p)

IsDuplicateDecl(p) == p \in program /\ \E q \in program : q = p /\ q # p

IsNonConstantInitializer(p) == p \in program /\ \E init \in p : init # Constant

IsIllegalLocalName(p) == p \in program /\ \E name \in p : name \notin program

Next ==
  /\ TranslateProgram
  /\ TypeOK'

Spec ==
  /\ Init
  /\ [][Next]_program
  /\ WF_vars(Next)

THEOREM Spec => []TypeOK
THEOREM Spec => SemanticPreservation
THEOREM Spec => SafetyProperties
THEOREM Spec => TerminationPreservation
THEOREM Spec => ErrorHandling

=============================================================================