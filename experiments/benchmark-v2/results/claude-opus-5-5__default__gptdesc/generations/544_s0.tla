------------------------------- MODULE SemaphoreIncrement -------------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat \ {0}

(* --algorithm SemaphoreIncrement
variables x = 0, sem = 1;

fair process proc \in 1..N
variable t = 0;
begin
lock:   await sem = 1;
        sem := 0;
p1:     t := x;
p2:     x := t + 1;
unlock: sem := 1;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES x, sem, pc, t

vars == << x, sem, pc, t >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ x = 0
        /\ sem = 1
        (* Process proc *)
        /\ t = [self \in 1..N |-> 0]
        /\ pc = [self \in ProcSet |-> "lock"]

lock(self) == /\ pc[self] = "lock"
              /\ sem = 1
              /\ sem' = 0
              /\ pc' = [pc EXCEPT ![self] = "p1"]
              /\ UNCHANGED << x, t >>

p1(self) == /\ pc[self] = "p1"
            /\ t' = [t EXCEPT ![self] = x]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << x, sem >>

p2(self) == /\ pc[self] = "p2"
            /\ x' = t[self] + 1
            /\ pc' = [pc EXCEPT ![self] = "unlock"]
            /\ UNCHANGED << sem, t >>

unlock(self) == /\ pc[self] = "unlock"
                /\ sem' = 1
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << x, t >>

proc(self) == lock(self) \/ p1(self) \/ p2(self) \/ unlock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..N: proc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(proc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(* Safety properties *)
TypeOK == /\ x \in Nat
          /\ sem \in {0, 1}
          /\ t \in [1..N -> Nat]
          /\ pc \in [ProcSet -> {"lock", "p1", "p2", "unlock", "Done"}]

MutualExclusion == \A i, j \in ProcSet :
                      (i # j) => ~(pc[i] \in {"p1", "p2", "unlock"} /\ pc[j] \in {"p1", "p2", "unlock"})

=============================================================================