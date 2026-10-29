------------------------------ MODULE NProcessMutex ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

ConstN     == 3
ConstProcs == 1..ConstN

ASSUME /\ N \in Nat
       /\ N >= 2
       /\ Procs = 1..N

Levels == 1..(N-1)

PCStates == {"ncs", "setlevel", "setvictim", "wait", "cs", "exit"}
TryStates == {"setlevel", "setvictim", "wait"}

VARIABLES pc, level, victim, cur

vars == <<pc, level, victim, cur>>

TypeOK ==
    /\ pc \in [Procs -> PCStates]
    /\ level \in [Procs -> 0..(N-1)]
    /\ victim \in [Levels -> Procs]
    /\ cur \in [Procs -> Levels]

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ level = [p \in Procs |-> 0]
    /\ victim = [l \in Levels |-> CHOOSE q \in Procs : TRUE]
    /\ cur = [p \in Procs |-> 1]

Try(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "setlevel"]
    /\ cur' = [cur EXCEPT ![p] = 1]
    /\ UNCHANGED <<level, victim>>

SetLevel(p) ==
    /\ pc[p] = "setlevel"
    /\ level' = [level EXCEPT ![p] = cur[p]]
    /\ pc' = [pc EXCEPT ![p] = "setvictim"]
    /\ UNCHANGED <<victim, cur>>

SetVictim(p) ==
    /\ pc[p] = "setvictim"
    /\ victim' = [victim EXCEPT ![cur[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED <<level, cur>>

CanAdvance(p) ==
    \/ victim[cur[p]] # p
    \/ \A k \in Procs \ {p} : level[k] < cur[p]

Wait(p) ==
    /\ pc[p] = "wait"
    /\ CanAdvance(p)
    /\ IF cur[p] = N - 1
          THEN /\ pc' = [pc EXCEPT ![p] = "cs"]
               /\ UNCHANGED cur
          ELSE /\ cur' = [cur EXCEPT ![p] = cur[p] + 1]
               /\ pc' = [pc EXCEPT ![p] = "setlevel"]
    /\ UNCHANGED <<level, victim>>

LeaveCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<level, victim, cur>>

Release(p) ==
    /\ pc[p] = "exit"
    /\ level' = [level EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED <<victim, cur>>

ProtocolStep(p) ==
    \/ SetLevel(p)
    \/ SetVictim(p)
    \/ Wait(p)
    \/ LeaveCS(p)
    \/ Release(p)

Proc(p) == Try(p) \/ ProtocolStep(p)

Next == \E p \in Procs : Proc(p)

Fairness == \A p \in Procs : WF_vars(ProtocolStep(p))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------------

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

Passed(p) ==
    CASE pc[p] \in {"cs", "exit"}                 -> N - 1
      [] pc[p] \in {"setlevel", "setvictim", "wait"} -> cur[p] - 1
      [] OTHER                                    -> 0

CSLevelInv ==
    \A p \in Procs : pc[p] \in {"cs", "exit"} => level[p] = N - 1

LevelInv ==
    \A p \in Procs :
        /\ pc[p] = "ncs" => level[p] = 0
        /\ pc[p] \in {"setvictim", "wait"} => level[p] = cur[p]
        /\ pc[p] = "setlevel" => level[p] = cur[p] - 1

FilterInv ==
    \A l \in Levels :
        Cardinality({p \in Procs : Passed(p) >= l}) <= N - l

Inv == TypeOK /\ CSLevelInv /\ LevelInv /\ FilterInv /\ MutualExclusion

StarvationFree ==
    \A p \in Procs : (pc[p] \in TryStates) ~> (pc[p] = "cs")

==================================================================================