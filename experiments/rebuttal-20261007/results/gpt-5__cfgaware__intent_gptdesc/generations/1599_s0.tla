----------------------------- MODULE FastMutex -----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES level, victim, phase, l

Proc == 1..N

Vars == << level, victim, phase, l >>

Init ==
  /\ level = [i \in Proc |-> 0]
  /\ victim = [k \in 1..(N-1) |-> 1]
  /\ phase = [i \in Proc |-> "ncs"]
  /\ l = [i \in Proc |-> 0]

TypeOK ==
  /\ level \in [Proc -> 0..(N-1)]
  /\ victim \in [1..(N-1) -> Proc]
  /\ phase \in [Proc -> {"ncs","set","wait","crit"}]
  /\ l \in [Proc -> 0..(N-1)]

MutualExclusion ==
  \A i \in Proc: \A j \in Proc:
    i # j => ~ (phase[i] = "crit" /\ phase[j] = "crit")

PhaseLevelConsistency ==
  /\ \A i \in Proc: phase[i] = "ncs" => /\ l[i] = 0 /\ level[i] = 0
  /\ \A i \in Proc: phase[i] \in {"set","wait"} => l[i] \in 1..(N-1)
  /\ \A i \in Proc:
        phase[i] = "crit" =>
          IF N = 1 THEN level[i] = 0 ELSE level[i] = N-1

Invariant == TypeOK /\ MutualExclusion /\ PhaseLevelConsistency

Try(i) ==
  /\ i \in Proc
  /\ phase[i] = "ncs"
  /\ IF N = 1 THEN
        /\ phase' = [phase EXCEPT ![i] = "crit"]
        /\ UNCHANGED << l, level, victim >>
     ELSE
        /\ l' = [l EXCEPT ![i] = 1]
        /\ phase' = [phase EXCEPT ![i] = "set"]
        /\ UNCHANGED << level, victim >>

SetStep(i) ==
  /\ i \in Proc
  /\ phase[i] = "set"
  /\ l[i] \in 1..(N-1)
  /\ LET li == l[i] IN
       /\ level' = [level EXCEPT ![i] = li]
       /\ victim' = [victim EXCEPT ![li] = i]
       /\ phase' = [phase EXCEPT ![i] = "wait"]
       /\ UNCHANGED l

WaitAdvance(i) ==
  /\ i \in Proc
  /\ phase[i] = "wait"
  /\ l[i] \in 1..(N-1)
  /\ LET li == l[i] IN
       /\ ~(\E j \in Proc: j # i /\ level[j] >= li /\ victim[li] = i)
       /\ IF li < N-1 THEN
            /\ l' = [l EXCEPT ![i] = li + 1]
            /\ phase' = [phase EXCEPT ![i] = "set"]
            /\ UNCHANGED << level, victim >>
          ELSE
            /\ phase' = [phase EXCEPT ![i] = "crit"]
            /\ UNCHANGED << l, level, victim >>

Exit(i) ==
  /\ i \in Proc
  /\ phase[i] = "crit"
  /\ level' = [level EXCEPT ![i] = 0]
  /\ l' = [l EXCEPT ![i] = 0]
  /\ phase' = [phase EXCEPT ![i] = "ncs"]
  /\ UNCHANGED victim

ProcStep(i) == Try(i) \/ SetStep(i) \/ WaitAdvance(i) \/ Exit(i)

Next == \E i \in Proc: ProcStep(i)

Spec == Init /\ [][Next]_Vars

Trying == \E i \in Proc: phase[i] \in {"set","wait"}
Entered == \E i \in Proc: phase[i] = "crit"

CondLiveness == [](Trying => <> Entered)

FairSpec ==
  Spec
  /\ \A i \in Proc:
       WF_Vars(SetStep(i))
     /\ WF_Vars(WaitAdvance(i))
     /\ WF_Vars(Exit(i))
=============================================================================