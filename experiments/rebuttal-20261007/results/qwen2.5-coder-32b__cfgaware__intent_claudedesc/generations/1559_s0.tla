---------------------------- MODULE AugmentedMutexLock ----------------------------

CONSTANTS N \* Number of processes (N = 2 for this problem)

VARIABLES pc, turn, history, stutterStep

\* Process identifiers
Proc == 1..N

\* Program counter values for the simple lock
PCValues == {"entry", "critical", "exit"}

\* Program counter values for Peterson's algorithm
PetersonPCValues == {"entry0", "entry1", "entry2", "critical", "exit"}

\* Initial predicate
Init == /\ pc = [p \in Proc |-> "entry"]
        /\ turn = 1
        /\ history = << >>
        /\ stutterStep = 0

\* Next-state relation for the simple lock with auxiliary variables
NextSimpleLock ==
    \/ /\ pc[1] = "entry"
       /\ stutterStep < 3
       /\ stutterStep' = stutterStep + 1
       /\ UNCHANGED <<pc, turn, history>>
    \/ /\ pc[1] = "entry"
       /\ stutterStep = 3
       /\ stutterStep' = 0
       /\ turn' = IF turn = 1 THEN 2 ELSE 1
       /\ history' = Append(history, turn')
       /\ pc' = [pc EXCEPT ![1] = "critical"]
    \/ /\ pc[1] = "critical"
       /\ pc' = [pc EXCEPT ![1] = "exit"]
    \/ /\ pc[1] = "exit"
       /\ pc' = [pc EXCEPT ![1] = "entry"]
    \/ /\ pc[2] = "entry"
       /\ stutterStep < 3
       /\ stutterStep' = stutterStep + 1
       /\ UNCHANGED <<pc, turn, history>>
    \/ /\ pc[2] = "entry"
       /\ stutterStep = 3
       /\ stutterStep' = 0
       /\ turn' = IF turn = 1 THEN 2 ELSE 1
       /\ history' = Append(history, turn')
       /\ pc' = [pc EXCEPT ![2] = "critical"]
    \/ /\ pc[2] = "critical"
       /\ pc' = [pc EXCEPT ![2] = "exit"]
    \/ /\ pc[2] = "exit"
       /\ pc' = [pc EXCEPT ![2] = "entry"]

\* Type correctness predicate
TypeOKHS ==
    /\ pc \in [Proc -> PCValues]
    /\ turn \in Proc
    /\ history \in Seq(Proc)
    /\ stutterStep \in 0..3

\* Invariant relating process positions and auxiliary variables to the turn ownership
LockInv ==
    \/ (\E p \in Proc : pc[p] = "entry" /\ stutterStep < 3)
    \/ (\A p \in Proc : pc[p] \notin {"entry", "critical"} => pc[p] = "exit")
    \/ (\A p \in Proc : pc[p] = "critical" => turn = p)

\* Specification for the simple lock with auxiliary variables
SpecHS == Init /\ [][NextSimpleLock]_<<pc, turn, history, stutterStep>>

\* Next-state relation for Peterson's algorithm
NextPeterson ==
    \/ /\ pc[1] = "entry0"
       /\ pc' = [pc EXCEPT ![1] = "entry1"]
    \/ /\ pc[1] = "entry1"
       /\ turn' = 1
       /\ pc' = [pc EXCEPT ![1] = "entry2"]
    \/ /\ pc[1] = "entry2"
       /\ (\A q \in Proc : q # 1 => pc[q] \notin {"entry1", "critical"})
       /\ pc' = [pc EXCEPT ![1] = "critical"]
    \/ /\ pc[1] = "critical"
       /\ pc' = [pc EXCEPT ![1] = "exit"]
    \/ /\ pc[1] = "exit"
       /\ pc' = [pc EXCEPT ![1] = "entry0"]
    \/ /\ pc[2] = "entry0"
       /\ pc' = [pc EXCEPT ![2] = "entry1"]
    \/ /\ pc[2] = "entry1"
       /\ turn' = 2
       /\ pc' = [pc EXCEPT ![2] = "entry2"]
    \/ /\ pc[2] = "entry2"
       /\ (\A q \in Proc : q # 2 => pc[q] \notin {"entry1", "critical"})
       /\ pc' = [pc EXCEPT ![2] = "critical"]
    \/ /\ pc[2] = "critical"
       /\ pc' = [pc EXCEPT ![2] = "exit"]
    \/ /\ pc[2] = "exit"
       /\ pc' = [pc EXCEPT ![2] = "entry0"]

\* Specification for Peterson's algorithm
PSpec == Init /\ [][NextPeterson]_<<pc, turn>>

\* Refinement mapping from simple lock to Peterson's algorithm
SimpleToPeterson ==
    \/ /\ pc[1] = "entry" /\ stutterStep < 3 => pc' = [p \in Proc |-> IF p = 1 THEN "entry0" ELSE "entry0"]
    \/ /\ pc[1] = "entry" /\ stutterStep = 3 => pc' = [p \in Proc |-> IF p = 1 THEN "entry2" ELSE "entry0"]
    \/ /\ pc[1] = "critical" => pc' = [p \in Proc |-> IF p = 1 THEN "critical" ELSE "entry0"]
    \/ /\ pc[1] = "exit" => pc' = [p \in Proc |-> IF p = 1 THEN "exit" ELSE "entry0"]
    \/ /\ pc[2] = "entry" /\ stutterStep < 3 => pc' = [p \in Proc |-> IF p = 2 THEN "entry0" ELSE "entry0"]
    \/ /\ pc[2] = "entry" /\ stutterStep = 3 => pc' = [p \in Proc |-> IF p = 2 THEN "entry2" ELSE "entry0"]
    \/ /\ pc[2] = "critical" => pc' = [p \in Proc |-> IF p = 2 THEN "critical" ELSE "entry0"]
    \/ /\ pc[2] = "exit" => pc' = [p \in Proc |-> IF p = 2 THEN "exit" ELSE "entry0"]

\* Refinement relation
Refines ==
    SpecHS => <<pc, turn>> \in PSpec

\* Complete specification with refinement check
Spec == SpecHS /\ Refines

=============================================================================