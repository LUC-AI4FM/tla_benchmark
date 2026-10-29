---------------------------- MODULE TwoChoiceLoop ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS k1, k2, c1, c2

CONSTANTS KEY, OPTIMISTIC_CLIENT, PESSIMISTIC_CLIENT,
          CLIENT_READ_KEY, CLIENT_WRITE_KEY, CLIENT_PRIMARY

VARIABLE x

vars == <<x>>

-----------------------------------------------------------------------------
(* Definitions used to bind constants in the model-checking configuration *)

Keys == {k1, k2}

OptimistiicClient == {c1}

PessimisticClient == {c2}

ClientReadKeys == [c \in {c1, c2} |-> {k1}]

ClientWriteKeys == [c \in {c1, c2} |-> {k2}]

ClientPrimary == [c \in {c1, c2} |-> k2]

-----------------------------------------------------------------------------
(* The one-variable transition system *)

Init == x = 0

Next == \/ /\ x = 0
           /\ x' \in {1, 2}
        \/ /\ x # 0
           /\ x' = 0

Spec == Init /\ [][Next]_x /\ WF_x(Next)

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK == x \in {0, 1, 2}

UniqueCommitOrAbort == x \in {0, 1, 2}

CommitConsistency == x # 1 \/ x # 2

AbortConsistency == x >= 0

WriteConsistency == x <= 2

UniqueLockOrWrite == ~(x = 1 /\ x = 2)

UniqueWrite == x \in Nat

OptimisticReadSnapshotIsolation == TypeOK

PessimisticReadSnapshotIsolation == TypeOK

MsgTsConsistency == TypeOK

-----------------------------------------------------------------------------
(* Temporal properties *)

StabilizeAwayFromOne == <>[](x # 1)

StabilizeAwayFromTwo == <>[](x # 2)

StabilizeAwayFromOneOrTwo == <>[](x # 1) \/ <>[](x # 2)

InfinitelyOftenZero == []<>(x = 0)

NegatedProperty == ~StabilizeAwayFromOneOrTwo

-----------------------------------------------------------------------------
(* Postcondition checking a counterexample trace encoded as records,
   tuples, and sets *)

CounterExample ==
    [ state  |-> { <<1, [x |-> 0]>>, <<2, [x |-> 1]>>, <<3, [x |-> 0]>> },
      action |-> { << <<1, [x |-> 0]>>, [name |-> "Next"], <<2, [x |-> 1]>> >>,
                   << <<2, [x |-> 1]>>, [name |-> "Next"], <<3, [x |-> 0]>> >>,
                   << <<3, [x |-> 0]>>, [name |-> "Next"], <<2, [x |-> 1]>> >> } ]

PostCondition ==
    /\ \A s \in CounterExample.state : s[2].x \in {0, 1, 2}
    /\ \A a \in CounterExample.action :
          \/ (a[1][2].x = 0 /\ a[3][2].x \in {1, 2})
          \/ (a[1][2].x # 0 /\ a[3][2].x = 0)
    /\ Cardinality(CounterExample.state) = 3

=============================================================================