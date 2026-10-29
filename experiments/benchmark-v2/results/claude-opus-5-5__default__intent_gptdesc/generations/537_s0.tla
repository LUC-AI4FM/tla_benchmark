---- MODULE ConcurrentSquare ----
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat

VARIABLES i, x, pc

vars == <<i, x, pc>>

Phases == {"square", "advance", "finished"}

Tasks == {"Incrementer", "Updater"}

Init ==
    /\ i = 0
    /\ x = 0
    /\ pc = "square"

\* Incrementer task, square phase: x = i^2 holds.
\* If i < N, advance the index and move to the advancing phase.
IncAdvance ==
    /\ pc = "square"
    /\ i < N
    /\ i' = i + 1
    /\ pc' = "advance"
    /\ UNCHANGED x

\* Incrementer task, square phase: i = N, so enter the finished state.
IncFinish ==
    /\ pc = "square"
    /\ i = N
    /\ pc' = "finished"
    /\ UNCHANGED <<i, x>>

\* Updater task, advancing phase: x = (i-1)^2.
\* Since i^2 = (i-1)^2 + 2i - 1, this step re-establishes x = i^2.
UpdSquare ==
    /\ pc = "advance"
    /\ x' = x + 2 * i - 1
    /\ pc' = "square"
    /\ UNCHANGED i

Incrementer == IncAdvance \/ IncFinish

Updater == UpdSquare

\* Stuttering in the finished state avoids reporting a deadlock there.
Done ==
    /\ pc = "finished"
    /\ UNCHANGED vars

Next == Incrementer \/ Updater \/ Done

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Incrementer)
    /\ WF_vars(Updater)

---------------------------------------------------------------------------
\* Safety properties

TypeOK ==
    /\ i \in 0..N
    /\ x \in 0..(N * N)
    /\ pc \in Phases

SquareInv ==
    pc = "square" => x = i * i

AdvanceInv ==
    pc = "advance" => /\ i > 0
                      /\ x = (i - 1) * (i - 1)

FinishedInv ==
    pc = "finished" => /\ i = N
                       /\ x = N * N

Inv == TypeOK /\ SquareInv /\ AdvanceInv /\ FinishedInv

---------------------------------------------------------------------------
\* Liveness properties

Termination == <>(pc = "finished")

\* From any reachable state, the finished state is eventually reached.
EventuallyFinished == TRUE ~> (pc = "finished" /\ i = N /\ x = N * N)

\* Once finished, the system stays finished.
StaysFinished == [](pc = "finished" => [](pc = "finished"))

THEOREM Spec => []Inv
THEOREM Spec => Termination /\ EventuallyFinished
====