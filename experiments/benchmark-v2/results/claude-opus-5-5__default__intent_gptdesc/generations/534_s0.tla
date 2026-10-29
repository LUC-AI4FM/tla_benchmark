------------------------------ MODULE FindMax ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Input,      \* the immutable input sequence of integers
          MinValue    \* a lower bound strictly below every element of Input

ASSUME InputIsSeqOfInts == Input \in Seq(Int)
ASSUME MinValueIsInt    == MinValue \in Int
ASSUME LowerBound       == \A i \in 1..Len(Input) : MinValue < Input[i]

VARIABLES cur,        \* current candidate for the maximum
          unseen,     \* set of indices not yet processed
          visits,     \* number of times each index has been processed
          pc          \* control state: "loop" or "done"

vars == <<cur, unseen, visits, pc>>

Indices == 1..Len(Input)

Range(s) == { s[i] : i \in 1..Len(s) }

Processed == Indices \ unseen

-----------------------------------------------------------------------------
(* Postcondition *)

IsMax(m) == /\ m \in Range(Input)
            /\ \A i \in Indices : m >= Input[i]

PostCondition ==
    IF Input = << >>
      THEN cur = MinValue
      ELSE IsMax(cur)

-----------------------------------------------------------------------------
(* Algorithm *)

Init == /\ cur = MinValue
        /\ unseen = Indices
        /\ visits = [i \in Indices |-> 0]
        /\ pc = "loop"

\* Inspect an arbitrary unprocessed index (nondeterministic order).
Step(i) == /\ pc = "loop"
           /\ i \in unseen
           /\ cur' = IF Input[i] > cur THEN Input[i] ELSE cur
           /\ unseen' = unseen \ {i}
           /\ visits' = [visits EXCEPT ![i] = @ + 1]
           /\ UNCHANGED pc

\* All indices processed: check the postcondition and halt.
Finish == /\ pc = "loop"
          /\ unseen = {}
          /\ Assert(PostCondition, "Postcondition violated: cur is not the maximum")
          /\ pc' = "done"
          /\ UNCHANGED <<cur, unseen, visits>>

\* Halting state: stutter forever (avoids deadlock reports).
Terminated == /\ pc = "done"
              /\ UNCHANGED vars

Next == \/ \E i \in unseen : Step(i)
        \/ Finish
        \/ Terminated

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ cur \in Int
          /\ unseen \subseteq Indices
          /\ visits \in [Indices -> 0..1]
          /\ pc \in {"loop", "done"}

\* The input is never modified (it is a constant); each index processed at most once,
\* and an index is marked processed exactly when it has been visited once.
ExactlyOnce == \A i \in Indices :
                   /\ visits[i] <= 1
                   /\ (i \in unseen <=> visits[i] = 0)

\* At termination every index has been processed exactly once.
AllProcessedAtEnd == pc = "done" => (unseen = {} /\ \A i \in Indices : visits[i] = 1)

\* Loop invariant: cur is the maximum of the processed prefix (or MinValue if none).
LoopInvariant ==
    /\ \A i \in Processed : cur >= Input[i]
    /\ \/ (Processed = {} /\ cur = MinValue)
       \/ (\E i \in Processed : cur = Input[i])

\* Partial correctness: at termination, the postcondition holds.
Correctness == pc = "done" => PostCondition

Inv == /\ TypeOK
       /\ ExactlyOnce
       /\ AllProcessedAtEnd
       /\ LoopInvariant
       /\ Correctness

-----------------------------------------------------------------------------
(* Liveness properties *)

\* The algorithm eventually terminates.
Termination == <>(pc = "done")

\* Every index is eventually processed.
AllEventuallyProcessed == <>(unseen = {})

\* Once terminated, it stays terminated with a correct result.
StableResult == [](pc = "done" => [](pc = "done" /\ PostCondition))

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM Spec => []Inv
THEOREM Spec => Termination
THEOREM Spec => AllEventuallyProcessed
=============================================================================