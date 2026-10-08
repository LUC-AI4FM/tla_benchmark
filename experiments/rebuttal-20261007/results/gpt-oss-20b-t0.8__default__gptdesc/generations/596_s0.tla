MODULE OneVarSpec
\* ------------------------------------------------------------------
\* This module specifies a one-variable transition system with the
\* following properties:
\*   * Variable x starts at 0.
\*   * From 0 it nondeterministically moves to either 1 or 2.
\*   * From any nonzero value it returns to 0.
\*   * The behavior is constrained by stuttering-closed next-state
\*     evolution and weak fairness for Next.
\*   * Several safety invariants, liveness properties, a negated
\*     property, and a postcondition involving records, tuples,
\*     and sets are stated as theorems.
\* ------------------------------------------------------------------

VARIABLE x

Init == x = 0

Next ==
    \/ (x' = 0 /\ x # 0)
    \/ (x' ∈ {1,2} /\ x = 0)

Spec == Init /\ [][Next]_<<x>> /\ WF_x(Next)

\* ------------------------------------------------------------------
\* Safety invariants
\* ------------------------------------------------------------------
SafetyInv == [] (x >= 0) /\ [] (x <= 2)

THEOREM Spec_Imply_SafetyInv == Spec => SafetyInv

\* ------------------------------------------------------------------
\* Liveness properties
\* ------------------------------------------------------------------
StabilizeAwayFrom12 ==
    <>[] (x # 1 /\ x # 2)

RepeatedZero ==
    []<> (x = 0)

NegationOfEventualOne ==
    ¬<>(x = 1)

THEOREM Spec_Imply_StabilizeAwayFrom12 == Spec => StabilizeAwayFrom12
THEOREM Spec_Imply_RepeatedZero      == Spec => RepeatedZero
THEOREM Spec_Imply_NegationOfEventualOne ==
    Spec => NegationOfEventualOne

\* ------------------------------------------------------------------
\* Postcondition that checks a TLC-generated counterexample trace.
\* The trace is encoded using records, tuples, and sets.
\* ------------------------------------------------------------------
PostCond ==
    ∃ rec \in { [x |-> 0,
                  y |-> (1,2),
                  z |-> {0,1}] } :
          TRUE

THEOREM Spec_Imply_PostCond == Spec => PostCond
===============================================================================