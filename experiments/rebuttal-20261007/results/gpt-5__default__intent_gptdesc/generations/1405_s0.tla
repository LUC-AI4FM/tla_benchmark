----------------------------- MODULE TwoComponentAtomicUpdate -----------------------------

EXTENDS Naturals, Sequences

CONSTANTS
  InitSeq, \* initial finite nonempty sequence of positive integers
  NonZero   \* fixed nonzero value (e.g., 1)

ASSUME
  /\ InitSeq \in Seq(Nat)
  /\ Len(InitSeq) \in Nat \ {0}
  /\ \A i \in 1..Len(InitSeq): InitSeq[i] \in Nat \ {0}
  /\ NonZero \in Nat \ {0}

VARIABLES seq, res

vars == << seq, res >>

RECURSIVE RemoveAll(_, _)
RemoveAll(s, v) ==
  IF Len(s) = 0 THEN << >>
  ELSE IF Head(s) = v
       THEN RemoveAll(Tail(s), v)
       ELSE <<Head(s)>> \o RemoveAll(Tail(s), v)

RECURSIVE RemSet(_)
RemSet(s) ==
  IF Len(s) = 0 THEN { << >> }
  ELSE
    LET rest == RemSet(Tail(s)) IN
      IF Head(s) = NonZero
      THEN { << >> \o t : t \in rest } \cup { <<Head(s)>> \o t : t \in rest }
      ELSE { <<Head(s)>> \o t : t \in rest }

Init ==
  /\ seq = InitSeq
  /\ res = 0

Inner ==
  /\ res = 0
  /\ res' = NonZero
  /\ seq' = RemoveAll(seq, NonZero)

Stutter ==
  /\ ~Enabled(Inner)
  /\ UNCHANGED vars

Next ==
  Inner \/ Stutter

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Inner)

\* Safety properties
TypeOK ==
  /\ seq \in Seq(Nat \ {0})
  /\ res \in {0, NonZero}

SeqSafety ==
  seq \in RemSet(InitSeq)

ResultRange ==
  [](res \in {0, NonZero})

ResultStability ==
  [](res = NonZero => res' = NonZero)

SeqAfterUpdate ==
  [](res = NonZero => seq = RemoveAll(InitSeq, NonZero))

Safety ==
  [] (TypeOK /\ SeqSafety) /\ ResultRange /\ ResultStability /\ SeqAfterUpdate

\* Liveness and termination/progress properties
Executed ==
  <> (res = NonZero /\ seq = RemoveAll(InitSeq, NonZero))

EventuallyDisabled ==
  <>[] (~Enabled(Inner))

Stable ==
  /\ res = NonZero
  /\ seq = RemoveAll(InitSeq, NonZero)

Termination ==
  <>[] Stable

==========================================================================================