---------------------------- MODULE ConcurrentIncrement ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

ConstN == 5

ASSUME N \in Nat \ {0}

Procs == 1..N

NoVal == -1

VARIABLES x, tmp, pc, lock

vars == << x, tmp, pc, lock >>

Init ==
    /\ x = 0
    /\ tmp = [p \in Procs |-> NoVal]
    /\ pc = [p \in Procs |-> "acquire"]
    /\ lock = 0

Acquire(p) ==
    /\ pc[p] = "acquire"
    /\ lock = 0
    /\ lock' = p
    /\ pc' = [pc EXCEPT ![p] = "read"]
    /\ UNCHANGED << x, tmp >>

Read(p) ==
    /\ pc[p] = "read"
    /\ tmp' = [tmp EXCEPT ![p] = x]
    /\ pc' = [pc EXCEPT ![p] = "write"]
    /\ UNCHANGED << x, lock >>

Write(p) ==
    /\ pc[p] = "write"
    /\ x' = tmp[p] + 1
    /\ pc' = [pc EXCEPT ![p] = "release"]
    /\ UNCHANGED << tmp, lock >>

Release(p) ==
    /\ pc[p] = "release"
    /\ lock' = 0
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED << x, tmp >>

Proc(p) == Acquire(p) \/ Read(p) \/ Write(p) \/ Release(p)

Terminating ==
    /\ \A p \in Procs : pc[p] = "Done"
    /\ UNCHANGED vars

Next == (\E p \in Procs : Proc(p)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A p \in Procs : WF_vars(Proc(p))

TypeOK ==
    /\ x \in 0..N
    /\ tmp \in [Procs -> (0..N) \cup {NoVal}]
    /\ pc \in [Procs -> {"acquire", "read", "write", "release", "Done"}]
    /\ lock \in 0..N

AddCorrect == (\A p \in Procs : pc[p] = "Done") => x = N

InCS(p) == pc[p] \in {"write", "release"} \/ (pc[p] = "read" /\ lock = p)

CriticalSecInv ==
    \A p, q \in Procs : (p # q) => ~(pc[p] \in {"write"} /\ pc[q] \in {"write"})
                                    /\ ~(InCS(p) /\ InCS(q))

=============================================================================