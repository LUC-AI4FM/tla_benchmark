```
MODULE Translation
EXTENDS Integers, Sequences, TLC

CONSTANTS 
  AST,        \* abstract syntax tree
  Processes,  \* set of process names
  Variables   \* set of variable names

VARIABLES 
  spec,       \* generated TLA+ specification
  translationOptions, \* fairness options for the translation output
  pc          \* program counter

Init ==
  /\ spec = << >>
  /\ translationOptions = "noFairness"
  /\ pc = 1

Next ==
  /\ IF (pc = 1) THEN 
    /\ WITH p \in Processes, v \in Variables DO
      /\ spec := spec ++ << "VARIABLE " << v << ";">>
    /\ pc := pc + 1
  ELSE IF (pc = 2) THEN 
    /\ WITH s \in AST DO
      /\ IF (s.type = "label") THEN
        /\ spec := spec ++ << "Label_" << s.label << ": ">>
      ELSE IF (s.type = "goto") THEN
        /\ spec := spec ++ << "Goto_" << s.target << "; ">>
    /\ pc := pc + 1
  ELSE IF (pc = 3) THEN 
    /\ WITH p \in Processes DO
      /\ IF (translationOptions = "weakFairnessProcessActions") THEN
        /\ spec := spec ++ << "FAIRNESS WeakProcessAction_" << p << ";">>
      ELSE IF (translationOptions = "strongFairnessProcessActions") THEN
        /\ spec := spec ++ << "FAIRNESS StrongProcessAction_" << p << ";">>
    /\ pc := pc + 1
  ELSE 
    /\ UNCHANGED <<spec, translationOptions, pc >>

Spec ==
  /\ Init
  /\ [][Next]_<<spec, translationOptions, pc>>
  /\ WF_vars(Next, <<pc>>)

THEOREM Spec => []Termination
Termination == (pc = 4)
```