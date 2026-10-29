---------------------------- MODULE MCPeterson ----------------------------
(***************************************************************************)
(* Model-checking configuration for Peterson's mutual exclusion algorithm *)
(* generalized to N processes (the "filter" algorithm).                   *)
(* The model is checked with N = 3, so Procs = {0, 1, 2}.                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(* With N = 3 this is the set {0, 1, 2} *)
Procs == 0 .. (N - 1)

(* Levels 1 .. N-1 that a process must pass through *)
Levels == 1 .. (N - 1)

VARIABLES
    level,   \* level[p]: current level of process p (0 = not competing)
    last,    \* last[l] : last process to arrive at level l (the victim)
    lv,      \* lv[p]   : level that process p is currently trying to pass
    pc       \* pc[p]   : program counter of process p

vars == << level, last, lv, pc >>

PCs == {"ncs", "enter", "setLevel", "setLast", "wait", "cs", "exit"}

TypeOK ==
    /\ level \in [Procs -> 0 .. (N - 1)]
    /\ last  \in [Levels -> Procs]
    /\ lv    \in [Procs -> Levels]
    /\ pc    \in [Procs -> PCs]

Init ==
    /\ level = [p \in Procs |-> 0]
    /\ last  = [l \in Levels |-> 0]
    /\ lv    = [p \in Procs |-> 1]
    /\ pc    = [p \in Procs |-> "ncs"]

(* Non-critical section: the process decides to try to enter *)
NCS(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "enter"]
    /\ UNCHANGED << level, last, lv >>

(* Start the entry protocol at level 1 *)
Enter(i) ==
    /\ pc[i] = "enter"
    /\ lv' = [lv EXCEPT ![i] = 1]
    /\ pc' = [pc EXCEPT ![i] = "setLevel"]
    /\ UNCHANGED << level, last >>

(* level[i] := l *)
SetLevel(i) ==
    /\ pc[i] = "setLevel"
    /\ level' = [level EXCEPT ![i] = lv[i]]
    /\ pc' = [pc EXCEPT ![i] = "setLast"]
    /\ UNCHANGED << last, lv >>

(* last[l] := i *)
SetLast(i) ==
    /\ pc[i] = "setLast"
    /\ last' = [last EXCEPT ![lv[i]] = i]
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED << level, lv >>

(* await (\A k # i : level[k] < l) \/ last[l] # i *)
Wait(i) ==
    /\ pc[i] = "wait"
    /\ \/ \A k \in Procs \ {i} : level[k] < lv[i]
       \/ last[lv[i]] # i
    /\ IF lv[i] < N - 1
          THEN /\ lv' = [lv EXCEPT ![i] = lv[i] + 1]
               /\ pc' = [pc EXCEPT ![i] = "setLevel"]
          ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
               /\ UNCHANGED lv
    /\ UNCHANGED << level, last >>

(* Critical section *)
CS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED << level, last, lv >>

(* Exit protocol: level[i] := 0 *)
Exit(i) ==
    /\ pc[i] = "exit"
    /\ level' = [level EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED << last, lv >>

(* Steps of the protocol proper (everything except leaving the NCS) *)
ProtocolStep(i) ==
    \/ Enter(i)
    \/ SetLevel(i)
    \/ SetLast(i)
    \/ Wait(i)
    \/ CS(i)
    \/ Exit(i)

Proc(i) == NCS(i) \/ ProtocolStep(i)

Next == \E i \in Procs : Proc(i)

(* Weak fairness on every protocol step; a process may stay in its       *)
(* non-critical section forever.                                         *)
Fairness == \A i \in Procs : WF_vars(ProtocolStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety: no two distinct processes are in the critical section at once *)
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Liveness: every process that reaches "enter" eventually reaches "cs" *)
StarvationFree ==
    \A i \in Procs : (pc[i] = "enter") ~> (pc[i] = "cs")

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => StarvationFree
=============================================================================