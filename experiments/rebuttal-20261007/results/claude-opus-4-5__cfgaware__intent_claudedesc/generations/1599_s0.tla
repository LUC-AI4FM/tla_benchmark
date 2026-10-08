---------------------------- MODULE MutualExclusion ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES pc, x, y, flags

vars == <<pc, x, y, flags>>

Procs == 1..N

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "start", "set_x", "check_y1", "set_y", "check_x", 
                          "wait_flags", "check_y2", "wait_y", "cs", "exit1", "exit2"}]
    /\ x \in 0..N
    /\ y \in 0..N
    /\ flags \in [Procs -> BOOLEAN]

Init ==
    /\ pc = [i \in Procs |-> "ncs"]
    /\ x = 0
    /\ y = 0
    /\ flags = [i \in Procs |-> FALSE]

NCS(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED <<x, y, flags>>

Start(i) ==
    /\ pc[i] = "start"
    /\ flags' = [flags EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "set_x"]
    /\ UNCHANGED <<x, y>>

SetX(i) ==
    /\ pc[i] = "set_x"
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "check_y1"]
    /\ UNCHANGED <<y, flags>>

CheckY1(i) ==
    /\ pc[i] = "check_y1"
    /\ IF y /= 0
       THEN /\ flags' = [flags EXCEPT ![i] = FALSE]
            /\ pc' = [pc EXCEPT ![i] = "wait_y"]
       ELSE /\ pc' = [pc EXCEPT ![i] = "set_y"]
            /\ UNCHANGED flags
    /\ UNCHANGED <<x, y>>

SetY(i) ==
    /\ pc[i] = "set_y"
    /\ y' = i
    /\ pc' = [pc EXCEPT ![i] = "check_x"]
    /\ UNCHANGED <<x, flags>>

CheckX(i) ==
    /\ pc[i] = "check_x"
    /\ IF x /= i
       THEN pc' = [pc EXCEPT ![i] = "wait_flags"]
       ELSE pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<x, y, flags>>

WaitFlags(i) ==
    /\ pc[i] = "wait_flags"
    /\ \A j \in Procs \ {i} : flags[j] = FALSE
    /\ pc' = [pc EXCEPT ![i] = "check_y2"]
    /\ UNCHANGED <<x, y, flags>>

CheckY2(i) ==
    /\ pc[i] = "check_y2"
    /\ IF y = i
       THEN pc' = [pc EXCEPT ![i] = "cs"]
       ELSE /\ flags' = [flags EXCEPT ![i] = FALSE]
            /\ pc' = [pc EXCEPT ![i] = "wait_y"]
    /\ UNCHANGED <<x, y>>

WaitY(i) ==
    /\ pc[i] = "wait_y"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED <<x, y, flags>>

CS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit1"]
    /\ UNCHANGED <<x, y, flags>>

Exit1(i) ==
    /\ pc[i] = "exit1"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![i] = "exit2"]
    /\ UNCHANGED <<x, flags>>

Exit2(i) ==
    /\ pc[i] = "exit2"
    /\ flags' = [flags EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<x, y>>

Step(i) ==
    \/ NCS(i)
    \/ Start(i)
    \/ SetX(i)
    \/ CheckY1(i)
    \/ SetY(i)
    \/ CheckX(i)
    \/ WaitFlags(i)
    \/ CheckY2(i)
    \/ WaitY(i)
    \/ CS(i)
    \/ Exit1(i)
    \/ Exit2(i)

Next == \E i \in Procs : Step(i)

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ \A i \in Procs : WF_vars(Step(i))

MutualExclusion == \A i, j \in Procs : (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Invariant == MutualExclusion

Trying(i) == pc[i] \in {"start", "set_x", "check_y1", "set_y", "check_x", 
                         "wait_flags", "check_y2", "wait_y"}

SomeTrying == \E i \in Procs : Trying(i)

SomeInCS == \E i \in Procs : pc[i] = "cs"

CondLiveness == SomeTrying ~> SomeInCS

================================================================================