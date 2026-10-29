------------------------------ MODULE Peterson ------------------------------
EXTENDS Naturals

(***************************************************************************)
(* Abstract lock specification, used as the target of a refinement        *)
(* mapping from Peterson's algorithm.                                     *)
(*                                                                         *)
(* --algorithm Lock {                                                      *)
(*   variable lock = 1;                                                    *)
(*   process (p \in {0,1}) {                                               *)
(*     a0: while (TRUE) {                                                  *)
(*     a1:   await lock = 1; lock := 0;                                    *)
(*     cs:   skip;                                                         *)
(*     a2:   lock := 1;                                                    *)
(*   } } }                                                                 *)
(***************************************************************************)
---------------------------------- MODULE Lock ----------------------------------
VARIABLES lock, pc

vars == << lock, pc >>

ProcSet == {0, 1}

Init == /\ lock = 1
        /\ pc = [self \in ProcSet |-> "a0"]

a0(self) == /\ pc[self] = "a0"
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED lock

a1(self) == /\ pc[self] = "a1"
            /\ lock = 1
            /\ lock' = 0
            /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED lock

a2(self) == /\ pc[self] = "a2"
            /\ lock' = 1
            /\ pc' = [pc EXCEPT ![self] = "a0"]

p(self) == a0(self) \/ a1(self) \/ cs(self) \/ a2(self)

Next == \E self \in ProcSet : p(self)

Spec == Init /\ [][Next]_vars

MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")
=================================================================================