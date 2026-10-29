---------------------------- MODULE MCSession9alt ----------------------------
(***************************************************************************)
(* Model-checking configuration for a mutual exclusion algorithm in the    *)
(* style of Session9alt. N processes compete for a critical section.       *)
(* The base algorithm is included inline (a ticket lock with modular       *)
(* tickets) so that this module is self-contained.                         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

(* Concrete model values: N = 3, Procs = {0, 1, 2} *)
const_N == 3

const_Procs == {0, 1, 2}

Procs == 0 .. (N - 1)

VARIABLES pc, next, serving, my

vars == << pc, next, serving, my >>

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "wait", "cs"}]
    /\ next \in 0 .. (N - 1)
    /\ serving \in 0 .. (N - 1)
    /\ my \in [Procs -> 0 .. (N - 1)]

Init ==
    /\ pc = [i \in Procs |-> "ncs"]
    /\ next = 0
    /\ serving = 0
    /\ my = [i \in Procs |-> 0]

(* Process i takes a ticket *)
Request(i) ==
    /\ pc[i] = "ncs"
    /\ my' = [my EXCEPT ![i] = next]
    /\ next' = (next + 1) % N
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED serving

(* Process i enters the critical section when its ticket is served *)
Enter(i) ==
    /\ pc[i] = "wait"
    /\ serving = my[i]
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED << next, serving, my >>

(* Process i leaves the critical section *)
Exit(i) ==
    /\ pc[i] = "cs"
    /\ serving' = (serving + 1) % N
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED << next, my >>

Proc(i) == Request(i) \/ Enter(i) \/ Exit(i)

Next == \E i \in Procs : Proc(i)

Fairness == \A i \in Procs : WF_vars(Proc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Properties checked                                                      *)
(***************************************************************************)
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

LivenessNaive ==
    \A i \in Procs : []<>(pc[i] = "cs")

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => LivenessNaive
=============================================================================