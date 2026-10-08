```
MODULE Translator
EXTENDS Integers, Sequences, TLC

CONSTANTS
  AST,
  Labels,
  Variables,
  Procedures,
  Parameters,
  Statements,
  ControlConstructs,
  ErrorConditions

VARIABLES
  state,
  pc,
  callStack,
  processInstances,
  enabledActions,
  errorFlag

Init ==
  /\ state = << >>
  /\ pc = "start"
  /\ callStack = << >>
  /\ processInstances = {}
  /\ enabledActions = {}
  /\ errorFlag = FALSE

Next ==
  /\ IF pc = "start" THEN
    /\ state := EvaluateAST(AST)
    /\ pc := "nextStatement"
  ELSE
    /\ IF pc = "nextStatement" THEN
      /\ WITH s \in Statements DO
        /\ IF IsEnabled(s, state) THEN
          /\ state := ApplyStatement(s, state)
          /\ pc := GetNextLabel(s)
        END
      END
    ELSE
      /\ IF pc = "procedureCall" THEN
        /\ WITH p \in Procedures DO
          /\ IF IsCallable(p, state) THEN
            /\ callStack := Append(callStack, p)
            /\ state := InitializeParameters(p, state)
            /\ pc := GetProcedureLabel(p)
          END
        END
      ELSE
        /\ IF pc = "procedureReturn" THEN
          /\ WITH p \in Procedures DO
            /\ IF IsReturnable(p, state) THEN
              /\ callStack := Tail(callStack)
              /\ state := RestoreState(p, state)
              /\ pc := GetNextLabel(p)
            END
          END
        ELSE
          /\ IF pc = "processInterleave" THEN
            /\ WITH pi \in processInstances DO
              /\ IF IsEnabled(pi, state) THEN
                /\ state := InterleaveProcess(pi, state)
                /\ pc := GetNextLabel(pi)
              END
            END
          ELSE
            /\ IF pc = "errorCondition" THEN
              /\ errorFlag := TRUE
              /\ UNCHANGED state
              /\ UNCHANGED pc
              /\ UNCHANGED callStack
              /\ UNCHANGED processInstances
              /\ UNCHANGED enabledActions
            END
  END

Spec ==
  /\ Init
  /\ [][Next]_state
  /\ WF_vars(Next)
  /\ SF_vars(Next)

THEOREM Spec => []ErrorFree
THEOREM Spec => <>Termination

ErrorFree == errorFlag = FALSE
Termination == pc = "end"

Fairness ==
  /\ WF_vars(Next)
  /\ SF_vars(Next)

IsEnabled(s, state) == 
  CASE s OF
    "if" => EvaluateCondition(s, state)
    "while" => EvaluateCondition(s, state)
    "either" => TRUE
    "when" => EvaluateCondition(s, state)
    "with" => TRUE
    OTHER => TRUE
  END

ApplyStatement(s, state) == 
  CASE s OF
    "if" => IF EvaluateCondition(s, state) THEN ApplyThenBranch(s, state) ELSE ApplyElseBranch(s, state)
    "while" => IF EvaluateCondition(s, state) THEN ApplyLoopBody(s, state) ELSE state
    "either" => ChooseEnabledAction(s, state)
    "when" => ApplyWhenBranch(s, state)
    "with" => ApplyWithBranch(s, state)
    OTHER => state
  END

EvaluateAST(AST) == 
  EvaluateDeclarations(AST) \cup EvaluateStatements(AST)

EvaluateDeclarations(AST) == 
  { decl \in AST : decl.type = "declaration" }

EvaluateStatements(AST) == 
  { stmt \in AST : stmt.type = "statement" }

GetNextLabel(s) == 
  CASE s OF
    "if" => IF EvaluateCondition(s, state) THEN GetThenLabel(s) ELSE GetElseLabel(s)
    "while" => IF EvaluateCondition(s, state) THEN GetLoopBodyLabel(s) ELSE GetEndLabel(s)
    "either" => ChooseNextLabel(s, state)
    "when" => GetWhenLabel(s)
    "with" => GetWithLabel(s)
    OTHER => GetNextStatementLabel(s)
  END

GetThenLabel(s) == 
  s.thenLabel

GetElseLabel(s) == 
  s.elseLabel

GetLoopBodyLabel(s) == 
  s.loopBodyLabel

GetEndLabel(s) == 
  s.endLabel

ChooseEnabledAction(s, state) == 
  CHOOSE a \in enabledActions : IsEnabled(a, state)

ChooseNextLabel(s, state) == 
  CHOOSE l \in Labels : IsEnabled(l, state)
```