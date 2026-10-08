MODULE SubtlePitfall
EXTENDS Naturals, Sequences

CONSTANT MAXLEN

VARIABLE state, log

StateValues == {"A", "B"}

Init ==
  /\ state = "A"
  /\ log = <<>>

Next ==
  LET newState == IF state = "A" THEN "B" ELSE "A" IN
    /\ state' = newState
    /\ log' = Append(log, state)
    /\ Len(log') <= MAXLEN

StateConstraint == Len(log) <= MAXLEN

Done == state = "Done"

LivenessProp == <> Done

Spec ==
  Init /\ [][Next]_<<state, log>> /\ WF_vars(Next)

SafetyInvariant == StateConstraint

FullSpec == Spec /\ SafetyInvariant

THEOREM LivenessFails: FullSpec => LivenessProp