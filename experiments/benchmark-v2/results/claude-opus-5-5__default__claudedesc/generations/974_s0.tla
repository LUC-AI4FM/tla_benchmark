------------------------------ MODULE SimpleRegular ------------------------------
(***************************************************************************)
(* A variant of the algorithm in module Simple, modified to use regular    *)
(* registers instead of atomic registers.  A regular register x[i] is      *)
(* modeled as a non-empty subset of {0,1}.  While a write of 1 over the    *)
(* old value 0 is in progress, the register holds {0,1}, and a concurrent  *)
(* read may return either value.  When the write completes, the register   *)
(* holds {1}.                                                              *)
(***************************************************************************)
EXTENDS Integers

CONSTANT N

ASSUME NAssump == (N \in Nat) /\ (N > 0)

(***************************************************************************
--algorithm SimpleRegular {
    variables x = [i \in 0..(N-1) |-> {0}], y = [i \in 0..(N-1) |-> 0] ;
    fair process (proc \in 0..N-1) {
      a1: x[self] := {0,1} ;
      a2: x[self] := {1} ;
      b:  with (v \in x[(self-1) % N]) { y[self] := v }
    }
}
***************************************************************************)

VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (0..N-1)

Init == /\ x = [i \in 0..(N-1) |-> {0}]
        /\ y = [i \in 0..(N-1) |-> 0]
        /\ pc = [self \in ProcSet |-> "a1"]

a1(self) == /\ pc[self] = "a1"
            /\ x' = [x EXCEPT ![self] = {0,1}]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ y' = y

a2(self) == /\ pc[self] = "a2"
            /\ x' = [x EXCEPT ![self] = {1}]
            /\ pc' = [pc EXCEPT ![self] = "b"]
            /\ y' = y

b(self) == /\ pc[self] = "b"
           /\ \E v \in x[(self-1) % N]:
                y' = [y EXCEPT ![self] = v]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x

proc(self) == a1(self) \/ a2(self) \/ b(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0..N-1: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Fairness == \A self \in 0..N-1 : WF_vars(proc(self))

FairSpec == Spec /\ Fairness

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety: when all processes have finished, some process has read 1.      *)
(***************************************************************************)
PCorrect == (\A i \in 0..(N-1) : pc[i] = "Done") =>
                (\E i \in 0..(N-1) : y[i] = 1)

TypeOK == /\ x \in [0..(N-1) -> (SUBSET {0, 1}) \ {{}}]
          /\ y \in [0..(N-1) -> {0,1}]
          /\ pc \in [0..(N-1) -> {"a1", "a2", "b", "Done"}]

Inv == /\ TypeOK
       /\ \A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = {1})
       /\ \/ \E i \in 0..(N-1) : pc[i] /= "Done"
          \/ \E i \in 0..(N-1) : y[i] = 1

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness theorems (proved with TLAPS using the inductive invariant   *)
(* Inv: Init => Inv, Inv /\ [Next]_vars => Inv', Inv => PCorrect).        *)
(***************************************************************************)
THEOREM InitInv == Init => Inv

THEOREM InvInductive == Inv /\ [Next]_vars => Inv'

THEOREM InvImpliesPCorrect == Inv => PCorrect

THEOREM Correctness == Spec => []PCorrect

THEOREM Correctness2 == Spec => []PCorrect

THEOREM FairTermination == FairSpec => Termination

(***************************************************************************)
(* Model-checking configuration:                                           *)
(*   CONSTANT N = 8                                                        *)
(*   SPECIFICATION Spec                                                    *)
(*   INVARIANTS PCorrect TypeOK Inv                                        *)
(***************************************************************************)
=============================================================================