```tla
MODULE AugmentedLock
EXTENDS Integers, TLC

CONSTANTS P, Q, Turn
VARIABLES pc, history, stutter, flagP, flagQ, turnOwner

Init ==
  /\ pc = [p \in {P, Q} |-> "entry"]
  /\ history = <<>>
  /\ stutter = [p \in {P, Q} |-> 0]
  /\ flagP = FALSE
  /\ flagQ = FALSE
  /\ turnOwner = P

Next ==
  /\ (pc[P] = "entry" /\ pc[Q] = "entry")
    => (pc' = [pc EXCEPT !.P = "critical"])
      /\ (stutter' = [stutter EXCEPT !.P = 1])
      /\ history' = Append(history, P)
      /\ flagP' = TRUE
      /\ UNCHANGED [flagQ, turnOwner]
  /\ (pc[P] = "entry" /\ stutter[P] = 1)
    => (pc' = [pc EXCEPT !.P = "critical"])
      /\ (stutter' = [stutter EXCEPT !.P = 2])
      /\ UNCHANGED history
      /\ flagQ' = TRUE
      /\ turnOwner' = P
      /\ UNCHANGED [flagP]
  /\ (pc[P] = "entry" /\ stutter[P] = 2)
    => (pc' = [pc EXCEPT !.P = "exit"])
      /\ (stutter' = [stutter EXCEPT !.P = 0])
      /\ UNCHANGED history
      /\ UNCHANGED flagP
      /\ UNCHANGED flagQ
      /\ turnOwner' = Q
  /\ (pc[Q] = "entry" /\ pc[P] = "critical")
    => (pc' = [pc EXCEPT !.Q = "critical"])
      /\ (stutter' = [stutter EXCEPT !.Q = 1])
      /\ history' = Append(history, Q)
      /\ flagP' = FALSE
      /\ flagQ' = TRUE
      /\ turnOwner' = Q
  /\ (pc[Q] = "entry" /\ stutter[Q] = 1)
    => (pc' = [pc EXCEPT !.Q = "critical"])
      /\ (stutter' = [stutter EXCEPT !.Q = 2])
      /\ UNCHANGED history
      /\ flagP' = FALSE
      /\ flagQ' = TRUE
      /\ turnOwner' = Q
      /\ UNCHANGED flagP
  /\ (pc[Q] = "entry" /\ stutter[Q] = 2)
    => (pc' = [pc EXCEPT !.Q = "exit"])
      /\ (stutter' = [stutter EXCEPT !.Q = 0])
      /\ UNCHANGED history
      /\ UNCHANGED flagP
      /\ UNCHANGED flagQ
      /\ turnOwner' = P
  /\ (pc[P] = "critical" /\ pc[Q] = "exit")
    => (pc' = [pc EXCEPT !.P = "exit"])
      /\ (stutter' = [stutter EXCEPT !.P = 0])
      /\ UNCHANGED history
      /\ flagP' = FALSE
      /\ UNCHANGED flagQ
      /\ turnOwner' = Q
  /\ (pc[Q] = "critical" /\ pc[P] = "exit")
    => (pc' = [pc EXCEPT !.Q = "exit"])
      /\ (stutter' = [stutter EXCEPT !.Q = 0])
      /\ UNCHANGED history
      /\ UNCHANGED flagP
      /\ flagQ' = FALSE
      /\ turnOwner' = P
  /\ (pc[P] = "exit" /\ pc[Q] = "entry")
    => (pc' = [pc EXCEPT !.P = "entry"])
      /\ (stutter' = [stutter EXCEPT !.P = 0])
      /\ history' = <<>>
      /\ flagP' = TRUE
      /\ UNCHANGED flagQ
      /\ turnOwner' = P
  /\ (pc[Q] = "exit" /\ pc[P] = "entry")
    => (pc' = [pc EXCEPT !.Q = "entry"])
      /\ (stutter' = [stutter EXCEPT !.Q = 0])
      /\ history' = <<>>
      /\ UNCHANGED flagP
      /\ flagQ' = TRUE
      /\ turnOwner' = Q
  /\ (pc[P] = "exit" /\ pc[Q] = "critical")
    => (pc' = [pc EXCEPT !.P = "entry"])
      /\ (stutter' = [stutter EXCEPT !.P = 0])
      /\ history' = <<>>
      /\ flagP' = TRUE
      /\ UNCHANGED flagQ
      /\ turnOwner' = P
  /\ (pc[Q] = "exit" /\ pc[P] = "critical")
    => (pc' = [pc EXCEPT !.Q = "entry"])
      /\ (stutter' = [stutter EXCEPT !.Q = 0])
      /\ history' = <<>>
      /\ UNCHANGED flagP
      /\ flagQ' = TRUE
      /\ turnOwner' = Q
  /\ OTHERWISE
    => UNCHANGED pc
      /\ UNCHANGED stutter
      /\ UNCHANGED history
      /\ UNCHANGED flagP
      /\ UNCHANGED flagQ
      /\ UNCHANGED turnOwner

Spec ==
  Init /\ [][Next]_<<pc, stutter, history, flagP, flagQ, turnOwner>>

THEOREM Spec => []<>(pc[P] = "critical")
THEOREM Spec => []<>(pc[Q] = "critical")

Fairness == <>[]<>(pc[P] = "entry" /\ pc[Q] = "exit") /\ <>[]<>(pc[Q] = "entry" /\ pc[P] = "exit")

Inv ==
  /\ (pc[P] = "critical" => turnOwner = P)
  /\ (pc[Q] = "critical" => turnOwner = Q)
  /\ (stutter[P] = 1 => history[Len(history)] = P)
  /\ (stutter[Q] = 1 => history[Len(history)] = Q)

TypeOK ==
  /\ pc \in [P |-> {"entry", "critical", "exit"}, Q |-> {"entry", "critical", "exit"}]
  /\ stutter \in [P |-> 0..2, Q |-> 0..2]
  /\ history \in Seq(P)
  /\ flagP \in BOOLEAN
  /\ flagQ \in BOOLEAN
  /\ turnOwner \in {P, Q}
```