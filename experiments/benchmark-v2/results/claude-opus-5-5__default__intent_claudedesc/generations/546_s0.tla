------------------------------ MODULE RoundRobinMutex ------------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

Procs == 0 .. (N - 1)

VARIABLES pc, turn

vars == << pc, turn >>

States == {"ncs", "wait", "cs"}

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ turn \in Procs

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ turn \in Procs

(* Process p finishes its non-critical work and starts waiting *)
RequestCS(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED turn

(* Process p enters the critical section when it holds the turn *)
EnterCS(p) ==
    /\ pc[p] = "wait"
    /\ turn = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED turn

(* Process p leaves the critical section and passes the turn on *)
ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ turn' = (p + 1) % N

Proc(p) == RequestCS(p) \/ EnterCS(p) \/ ExitCS(p)

Next == \E p \in Procs : Proc(p)

Fairness == \A p \in Procs : WF_vars(Proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

(* Safety *)
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Auxiliary invariant: only the turn holder can be in the critical section *)
CSImpliesTurn ==
    \A p \in Procs : pc[p] = "cs" => turn = p

(* Liveness *)
EveryProcessGetsTurn ==
    \A p \in Procs : []<>(turn = p)

StarvationFreedom ==
    \A p \in Procs : (pc[p] = "wait") ~> (pc[p] = "cs")

EventuallyEntersCS ==
    \A p \in Procs : []<>(pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion /\ CSImpliesTurn)
THEOREM Spec => (EveryProcessGetsTurn /\ StarvationFreedom /\ EventuallyEntersCS)

=============================================================================