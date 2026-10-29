------------------------------- MODULE Peterson -------------------------------
EXTENDS Integers, TLAPS

VARIABLES flag, turn, pc

vars == <<flag, turn, pc>>

ProcSet == {1, 2}

Other(p) == IF p = 1 THEN 2 ELSE 1

Labels == {"a1", "a2", "a3", "cs", "a4"}

TypeOK ==
  /\ flag \in [ProcSet -> BOOLEAN]
  /\ turn \in ProcSet
  /\ pc \in [ProcSet -> Labels]

Init ==
  /\ flag = [i \in ProcSet |-> FALSE]
  /\ turn = 1
  /\ pc = [i \in ProcSet |-> "a1"]

\* Signal intent
a1(p) ==
  /\ pc[p] = "a1"
  /\ flag' = [flag EXCEPT ![p] = TRUE]
  /\ pc' = [pc EXCEPT ![p] = "a2"]
  /\ UNCHANGED turn

\* Yield the turn to the other process
a2(p) ==
  /\ pc[p] = "a2"
  /\ turn' = Other(p)
  /\ pc' = [pc EXCEPT ![p] = "a3"]
  /\ UNCHANGED flag

\* Wait until the other is not interested or it is our turn
a3(p) ==
  /\ pc[p] = "a3"
  /\ \/ flag[Other(p)] = FALSE
     \/ turn = p
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED <<flag, turn>>

\* Critical section
cs(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "a4"]
  /\ UNCHANGED <<flag, turn>>

\* Retract intent
a4(p) ==
  /\ pc[p] = "a4"
  /\ flag' = [flag EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "a1"]
  /\ UNCHANGED turn

proc(p) == a1(p) \/ a2(p) \/ a3(p) \/ cs(p) \/ a4(p)

Next == \E p \in ProcSet : proc(p)

Spec == Init /\ [][Next]_vars /\ \A p \in ProcSet : WF_vars(proc(p))

-----------------------------------------------------------------------------
MutualExclusion == ~(pc[1] = "cs" /\ pc[2] = "cs")

I ==
  \A p \in ProcSet :
     /\ flag[p] <=> (pc[p] \in {"a2", "a3", "cs", "a4"})
     /\ pc[p] \in {"cs", "a4"} =>
           \/ turn = p
           \/ pc[Other(p)] \notin {"a3", "cs", "a4"}

Inv == TypeOK /\ I

THEOREM InvMutex == Inv => MutualExclusion
  BY DEF Inv, I, TypeOK, MutualExclusion, ProcSet, Other

THEOREM InvInductive == Spec => []Inv
<1>1. Init => Inv
  BY DEF Init, Inv, I, TypeOK, ProcSet, Labels, Other
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. ASSUME NEW p \in ProcSet, a1(p) PROVE Inv'
    BY <2>1 DEF Inv, I, TypeOK, a1, ProcSet, Labels, Other
  <2>2. ASSUME NEW p \in ProcSet, a2(p) PROVE Inv'
    BY <2>2 DEF Inv, I, TypeOK, a2, ProcSet, Labels, Other
  <2>3. ASSUME NEW p \in ProcSet, a3(p) PROVE Inv'
    BY <2>3 DEF Inv, I, TypeOK, a3, ProcSet, Labels, Other
  <2>4. ASSUME NEW p \in ProcSet, cs(p) PROVE Inv'
    BY <2>4 DEF Inv, I, TypeOK, cs, ProcSet, Labels, Other
  <2>5. ASSUME NEW p \in ProcSet, a4(p) PROVE Inv'
    BY <2>5 DEF Inv, I, TypeOK, a4, ProcSet, Labels, Other
  <2>6. CASE UNCHANGED vars
    BY <2>6 DEF Inv, I, TypeOK, vars, Other
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next, proc
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(* Abstract lock specification, via the refinement mapping lck. *)

lck == IF pc[1] = "cs" THEN 1 ELSE IF pc[2] = "cs" THEN 2 ELSE 0

LInit == lck = 0

Acquire(p) == lck = 0 /\ lck' = p
Release(p) == lck = p /\ lck' = 0

LNext == \E p \in ProcSet : Acquire(p) \/ Release(p)

LSpec == LInit /\ [][LNext]_lck

THEOREM Refinement == Spec => LSpec
<1>1. Init => LInit
  BY DEF Init, LInit, lck, ProcSet
<1>2. Inv /\ Inv' /\ [Next]_vars => [LNext]_lck
  <2> SUFFICES ASSUME Inv, Inv', [Next]_vars PROVE [LNext]_lck
    OBVIOUS
  <2>1. ASSUME NEW p \in ProcSet, a1(p) PROVE [LNext]_lck
    BY <2>1 DEF Inv, I, TypeOK, a1, lck, LNext, Acquire, Release, ProcSet, Other
  <2>2. ASSUME NEW p \in ProcSet, a2(p) PROVE [LNext]_lck
    BY <2>2 DEF Inv, I, TypeOK, a2, lck, LNext, Acquire, Release, ProcSet, Other
  <2>3. ASSUME NEW p \in ProcSet, a3(p) PROVE [LNext]_lck
    BY <2>3 DEF Inv, I, TypeOK, a3, lck, LNext, Acquire, Release, ProcSet, Other
  <2>4. ASSUME NEW p \in ProcSet, cs(p) PROVE [LNext]_lck
    BY <2>4 DEF Inv, I, TypeOK, cs, lck, LNext, Acquire, Release, ProcSet, Other
  <2>5. ASSUME NEW p \in ProcSet, a4(p) PROVE [LNext]_lck
    BY <2>5 DEF Inv, I, TypeOK, a4, lck, LNext, Acquire, Release, ProcSet, Other
  <2>6. CASE UNCHANGED vars
    BY <2>6 DEF vars, lck
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next, proc
<1>3. QED
  BY <1>1, <1>2, InvInductive, PTL DEF Spec, LSpec

=============================================================================