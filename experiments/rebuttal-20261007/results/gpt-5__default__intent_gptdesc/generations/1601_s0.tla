---- MODULE FischerTimed ----
EXTENDS Naturals

CONSTANTS N, LONG, SHORT, INF

ASSUME
  /\ N \in Nat \ {0}
  /\ LONG \in Nat
  /\ SHORT \in Nat
  /\ LONG >= SHORT
  /\ INF \notin Nat

Proc == 1..N
TimerVals == Nat \cup {INF}

VARIABLES pc, t, reg

vars == << pc, t, reg >>

Init ==
  /\ pc = [ i \in Proc |-> "NCS" ]
  /\ t  = [ i \in Proc |-> INF ]
  /\ reg = 0

Tick ==
  /\ pc' = pc
  /\ reg' = reg
  /\ t' = [ i \in Proc |->
              IF t[i] = INF THEN INF
              ELSE IF t[i] = 0 THEN 0 ELSE t[i] - 1 ]

StartTry(i) ==
  /\ i \in Proc
  /\ pc[i] = "NCS"
  /\ pc' = [pc EXCEPT ![i] = "Trying"]
  /\ t'  = [t  EXCEPT ![i] = LONG]
  /\ UNCHANGED reg

Reserve(i) ==
  /\ i \in Proc
  /\ pc[i] = "Trying"
  /\ t[i] = 0
  /\ reg = 0
  /\ reg' = i
  /\ pc' = [pc EXCEPT ![i] = "Hold"]
  /\ t'  = [t  EXCEPT ![i] = SHORT]

Enter(i) ==
  /\ i \in Proc
  /\ pc[i] = "Hold"
  /\ t[i] = 0
  /\ reg = i
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED <<reg, t>>

Abort(i) ==
  /\ i \in Proc
  /\ pc[i] = "Hold"
  /\ t[i] = 0
  /\ reg # i
  /\ pc' = [pc EXCEPT ![i] = "NCS"]
  /\ UNCHANGED <<reg, t>>

Exit(i) ==
  /\ i \in Proc
  /\ pc[i] = "CS"
  /\ reg' = 0
  /\ pc' = [pc EXCEPT ![i] = "NCS"]
  /\ UNCHANGED t

ProcStep(i) == StartTry(i) \/ Reserve(i) \/ Enter(i) \/ Abort(i) \/ Exit(i)

Next == Tick \/ (\E i \in Proc : ProcStep(i))

TypeOK ==
  /\ pc \in [Proc -> {"NCS","Trying","Hold","CS"}]
  /\ t \in [Proc -> TimerVals]
  /\ reg \in ({0} \cup Proc)

InCS(i) == pc[i] = "CS"
Attempting(i) == pc[i] \in {"Trying","Hold"}

MutualExclusion ==
  \A i, j \in Proc : (i # j) => ~(InCS(i) /\ InCS(j))

Safety == [](TypeOK /\ MutualExclusion)
MutualExclAlways == []MutualExclusion

FairTick == SF_vars(Tick)
FairProc == \A i \in Proc : SF_vars(ProcStep(i))

EventualEntry ==
  \A i \in Proc : (<>[] Attempting(i)) => (<> InCS(i))

WitnessTwoInCS ==
  <>(\E i, j \in Proc : i # j /\ InCS(i) /\ InCS(j))

ClaimedButNeverEnters(i) ==
  <>(reg = i /\ [] ~InCS(i))

ExistsClaimedButNeverEnters ==
  \E i \in Proc : <>(reg = i /\ [] ~InCS(i))

Spec == Init /\ [][Next]_vars /\ FairTick /\ FairProc
====