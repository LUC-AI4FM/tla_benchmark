---- MODULE ReusableBarrier ----
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Procs == 1..N

States == {"working", "waiting", "released"}

VARIABLES pc, arrivedAt, gen, count

vars == <<pc, arrivedAt, gen, count>>

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ arrivedAt \in [Procs -> {0, 1}]
    /\ gen \in {0, 1}
    /\ count \in 0..(N - 1)

Flip(b) == 1 - b

Init ==
    /\ pc = [p \in Procs |-> "working"]
    /\ arrivedAt = [p \in Procs |-> 1]
    /\ gen = 0
    /\ count = 0

Arrive(p) ==
    /\ pc[p] = "working"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ arrivedAt' = [arrivedAt EXCEPT ![p] = gen]
    /\ IF count + 1 = N
          THEN /\ count' = 0
               /\ gen' = Flip(gen)
          ELSE /\ count' = count + 1
               /\ gen' = gen

Release(p) ==
    /\ pc[p] = "waiting"
    /\ arrivedAt[p] # gen
    /\ pc' = [pc EXCEPT ![p] = "released"]
    /\ UNCHANGED <<arrivedAt, gen, count>>

Continue(p) ==
    /\ pc[p] = "released"
    /\ pc' = [pc EXCEPT ![p] = "working"]
    /\ UNCHANGED <<arrivedAt, gen, count>>

Next == \E p \in Procs : Arrive(p) \/ Release(p) \/ Continue(p)

Fairness ==
    \A p \in Procs :
        /\ WF_vars(Arrive(p))
        /\ WF_vars(Release(p))
        /\ WF_vars(Continue(p))

Spec == Init /\ [][Next]_vars /\ Fairness

CountInvariant ==
    /\ count = Cardinality({p \in Procs : pc[p] = "waiting" /\ arrivedAt[p] = gen})
    /\ count < N

NoPrematureRelease ==
    \A p \in Procs :
        pc[p] = "released" =>
            /\ arrivedAt[p] # gen
            /\ \A q \in Procs :
                  \/ arrivedAt[q] = arrivedAt[p]
                  \/ (pc[q] = "waiting" /\ arrivedAt[q] = gen)

NoCrossInstanceMixing ==
    \A p, q \in Procs :
        (pc[p] = "released" /\ pc[q] = "released") => arrivedAt[p] = arrivedAt[q]

WaitingConsistency ==
    \A p \in Procs :
        (pc[p] = "waiting" /\ arrivedAt[p] # gen) =>
            \A q \in Procs : arrivedAt[q] = arrivedAt[p] \/ (pc[q] = "waiting" /\ arrivedAt[q] = gen)

Safety ==
    /\ TypeOK
    /\ CountInvariant
    /\ NoPrematureRelease
    /\ NoCrossInstanceMixing
    /\ WaitingConsistency

EventualRelease ==
    \A p \in Procs : (pc[p] = "waiting") ~> (pc[p] = "released")

EventualReuse ==
    /\ \A p \in Procs : []<>(pc[p] = "released")
    /\ []<>(gen = 0)
    /\ []<>(gen = 1)

====