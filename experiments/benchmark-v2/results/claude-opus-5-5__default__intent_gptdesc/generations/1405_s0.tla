------------------------------ MODULE InnerOuterService ------------------------------
(***************************************************************************)
(* An outer controller and a single inner service share two variables:    *)
(*   - seq    : a sequence of integers                                     *)
(*   - result : an integer                                                 *)
(*                                                                         *)
(* The inner service has one atomic action. It sets result from 0 to the   *)
(* fixed nonzero value NewVal. In the same step it removes every           *)
(* occurrence of NewVal from the shared sequence.                          *)
(*                                                                         *)
(* The outer controller may only stutter, and only when the inner service  *)
(* is disabled. The inner service is weakly fair.                          *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS
    InitSeq,    \* the initial, finite, nonempty sequence of positive integers
    NewVal      \* the specific nonzero value written by the inner service

ASSUME InitAssumptions ==
    /\ InitSeq \in Seq(Int)
    /\ Len(InitSeq) > 0
    /\ \A i \in 1..Len(InitSeq) : InitSeq[i] > 0
    /\ NewVal \in Int
    /\ NewVal # 0

VARIABLES
    seq,        \* shared sequence (outer state; inner copy is the same value)
    result      \* shared result (outer state; inner result is the same value)

vars == << seq, result >>

---------------------------------------------------------------------------
(* Helper operators                                                         *)
---------------------------------------------------------------------------

\* Test operator for SelectSeq: keep elements different from NewVal
NotNewVal(x) == x # NewVal

\* Remove every occurrence of NewVal from a sequence
RemoveNewVal(s) == SelectSeq(s, NotNewVal)

\* TRUE iff t can be obtained from s by deleting zero or more elements
\* that are equal to NewVal (and nothing else).
RECURSIVE ObtainedByRemoving(_, _)
ObtainedByRemoving(s, t) ==
    IF s = << >>
    THEN t = << >>
    ELSE \/ /\ t # << >>
            /\ Head(s) = Head(t)
            /\ ObtainedByRemoving(Tail(s), Tail(t))
         \/ /\ Head(s) = NewVal
            /\ ObtainedByRemoving(Tail(s), t)

\* The sequence contains no occurrence of NewVal
NoNewValIn(s) == \A i \in 1..Len(s) : s[i] # NewVal

---------------------------------------------------------------------------
(* Initial state                                                            *)
---------------------------------------------------------------------------
Init ==
    /\ seq = InitSeq
    /\ result = 0

---------------------------------------------------------------------------
(* Inner service: atomic update on the shared state                        *)
---------------------------------------------------------------------------
InnerUpdate ==
    /\ result = 0
    /\ result' = NewVal
    /\ seq' = RemoveNewVal(seq)

---------------------------------------------------------------------------
(* Outer controller: stutter only when the inner service is disabled       *)
---------------------------------------------------------------------------
OuterStutter ==
    /\ ~ENABLED InnerUpdate
    /\ UNCHANGED vars

Next == InnerUpdate \/ OuterStutter

\* The inner service is a fair component (weak fairness)
Fairness == WF_vars(InnerUpdate)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety properties                                                        *)
---------------------------------------------------------------------------

TypeOK ==
    /\ seq \in Seq(Int)
    /\ result \in Int

\* result only ever takes the value 0 or NewVal
ResultValues == result \in {0, NewVal}

\* seq is always InitSeq with zero or more occurrences of NewVal removed
SeqIsFilteredOriginal == ObtainedByRemoving(InitSeq, seq)

\* A stronger invariant linking the two shared variables
Coupling ==
    /\ (result = 0      => seq = InitSeq)
    /\ (result = NewVal => seq = RemoveNewVal(InitSeq))

SafetyInv ==
    /\ TypeOK
    /\ ResultValues
    /\ SeqIsFilteredOriginal
    /\ Coupling

\* result changes only from 0 to NewVal
ResultChangesOnlyOnce ==
    [][result' # result => (result = 0 /\ result' = NewVal)]_vars

\* seq changes only by removing all occurrences of NewVal
SeqChangesOnlyByRemoval ==
    [][seq' # seq => seq' = RemoveNewVal(seq)]_vars

---------------------------------------------------------------------------
(* Liveness and termination                                                 *)
---------------------------------------------------------------------------

\* Stable, terminal state: the update has happened and no NewVal remains
Done ==
    /\ result = NewVal
    /\ NoNewValIn(seq)

\* The inner service eventually executes
EventuallyExecutes == <>(result = NewVal)

\* The system eventually reaches a state where the inner service is disabled
EventuallyDisabled == <>(~ENABLED InnerUpdate)

\* The system eventually reaches Done and stays there forever
EventuallyStable == <>[]Done

\* Once Done holds, it holds forever
DoneIsStable == [](Done => []Done)

\* Once Done holds, every further step only stutters
OnlyStutterAfterDone == [][Done => UNCHANGED vars]_vars

\* In Done, no inner action is enabled
DoneMeansDisabled == Done => ~ENABLED InnerUpdate

---------------------------------------------------------------------------
(* Theorems                                                                 *)
---------------------------------------------------------------------------
THEOREM Spec => []SafetyInv
THEOREM Spec => ResultChangesOnlyOnce /\ SeqChangesOnlyByRemoval
THEOREM Spec => []DoneMeansDisabled
THEOREM Spec => EventuallyExecutes /\ EventuallyDisabled
THEOREM Spec => EventuallyStable /\ DoneIsStable /\ OnlyStutterAfterDone

=============================================================================