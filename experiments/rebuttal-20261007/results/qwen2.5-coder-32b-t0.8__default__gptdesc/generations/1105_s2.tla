------------------------------- MODULE AsyncCommit -----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    Procs \* Set of processes
    F       \* Set of faulty processes

VARIABLES 
    votes   \* [Procs -> {"YES", "NO"}], initial vote of each process
    out     \* [Procs -> [Procs -> {"YES", "NO", "ABORT", "COMMIT"}]], messages sent by each process to others
    sus     \* [Procs -> Procs], suspicion relation, sus[p][q] means p suspects q

Init == 
    /\ votes \in [Procs -> {"YES", "NO"}]
    /\ out \in [Procs -> [Procs -> {}]]
    /\ sus \in [Procs -> (Procs)]
    /\ \/ (\A p \in Procs : votes[p] = "YES")
       \/ (\A p \in Procs : votes[p] = "NO")

Next == 
    \/ \E p \in Procs, q \in (Procs \ {p}), m \in {"YES", "NO"} :
        /\ out' = [out EXCEPT ![p][q] = m]
        /\ UNCHANGED <<votes, sus>>
    \/ \E p \in Procs, q \in F : 
        /\ sus' = [sus EXCEPT ![p][q] = TRUE]
        /\ UNCHANGED <<votes, out>>
    \/ \E p \in Procs :
        /\ (\A q \in (Procs \ {p}) : sus[p][q] => out'[p][q] = "ABORT")
        /\ UNCHANGED <<votes, sus>>

Spec == 
    WF_<<ProcAct>>_<>(Init /\ [][Next]_<<ProcAct>>)

ProcAct == 
    {act \in Actions : Enabled(act)}

Actions == 
    UNION { { [p \in Procs, q \in (Procs \ {p}), m \in {"YES", "NO"} | -> out[p][q]' = m ] },
            { [p \in Procs, q \in F | -> sus[p][q]' = TRUE ] },
            { [p \in Procs | -> (\A q \in (Procs \ {p}) : sus[p][q] => out[p][q]' = "ABORT") ] } }

TypeInvariant == 
    /\ votes \in [Procs -> {"YES", "NO"}]
    /\ out \in [Procs -> [Procs -> {}]]
    /\ sus \in [Procs -> (Procs)]

Agreement == 
    \/ (\A p, q \in Procs : out[p][q] = "COMMIT" => out[q][p] = "COMMIT")
    \/ (\A p, q \in Procs : out[p][q] = "ABORT" => out[q][p] = "ABORT")

AbortValidity == 
    /\ F /= {}
    /\ (\E p \in Procs : (\A q \in (Procs \ {p}) : sus[p][q]) => (\A r \in Procs : out[p][r] = "ABORT"))

CommitValidity == 
    /\ F = {}
    /\ (\A p, q \in Procs : votes[p] = "YES" => out[p][q] = "COMMIT")

Termination == 
    (\A p \in Procs : \/ out[p] = [q \in Procs |-> "ABORT"] \/ out[p] = [q \in Procs |-> "COMMIT"])

EventualCommit == 
    <>(\E p, q \in Procs : out[p][q] = "COMMIT")

Invariant == 
    Spec /\ TypeInvariant

Liveness == 
    WeakFairness(ProcAct)

=============================================================================