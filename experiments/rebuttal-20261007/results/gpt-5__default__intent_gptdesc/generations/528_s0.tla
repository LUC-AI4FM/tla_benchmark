----------------------------- MODULE OneShotUpdate -----------------------------
EXTENDS Integers, Sequences

CONSTANTS UnusedConstant

VARIABLES S, Q

SymUniverse == {"alpha", "beta", "gamma"}

SInit == {"alpha", "beta"}
SFinal == {"alpha", "beta", "gamma"}

QInit == <<1, 2, 3>>
QFinal == <<1, 42, 3>>

Init ==
  /\ S = SInit
  /\ Q = QInit

Update ==
  /\ S = SInit
  /\ Q = QInit
  /\ S' = SFinal
  /\ Q' = QFinal

Stutter ==
  /\ S' = S
  /\ Q' = Q

Next == Update \/ Stutter

vars == <<S, Q>>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Update)

TypeInv ==
  /\ S \in SUBSET SymUniverse
  /\ Len(Q) = 3
  /\ \A i \in 1..3: Q[i] \in Int

Final ==
  /\ S = SFinal
  /\ Q = QFinal

OnlyUpdateChanges ==
  [] ( ((S' # S) \/ (Q' # Q)) => Update )

Safety == []TypeInv /\ OnlyUpdateChanges

Liveness == <> Final
=============================================================================