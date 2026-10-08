MODULE SquareCheck
EXTENDS Naturals

VARIABLES x, done

\*--algorithm SquareCheckAlg {
  variables x, done;
  Init ==
    /\ x \in 1..10
    /\ done = FALSE;
  Next ==
    IF NOT done THEN
      ASSERT (x * x <= 100);
      done' = TRUE;
    ELSE
      UNCHANGED <<x,done>>;
}

\*--end algorithm

Spec == Init /\ [][Next]_<<x,done>>;

Termination == [] <> done;

THEOREM TerminationIsSatisfied == Spec => Termination;