---------------------------- MODULE PetersonN ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Procs == 0..(N-1)

VARIABLES level, last_to_enter, pc, l

vars == << level, last_to_enter, pc, l >>

ProcSet == Procs

Init == /\ level = [i \in Procs |-> -1]
        /\ last_to_enter = [i \in 0..(N-2) |-> 0]
        /\ l = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ UNCHANGED << level, last_to_enter, l >>

enter(self) == /\ pc[self] = "enter"
               /\ l' = [l EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self] = "lvl"]
               /\ UNCHANGED << level, last_to_enter >>

lvl(self) == /\ pc[self] = "lvl"
             /\ IF l[self] < N - 1
                   THEN /\ level' = [level EXCEPT ![self] = l[self]]
                        /\ pc' = [pc EXCEPT ![self] = "last"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                        /\ level' = level
             /\ UNCHANGED << last_to_enter, l >>

last(self) == /\ pc[self] = "last"
              /\ last_to_enter' = [last_to_enter EXCEPT ![l[self]] = self]
              /\ pc' = [pc EXCEPT ![self] = "wait"]
              /\ UNCHANGED << level, l >>

wait(self) == /\ pc[self] = "wait"
              /\ \/ last_to_enter[l[self]] # self
                 \/ \A k \in Procs \ {self} : level[k] < l[self]
              /\ l' = [l EXCEPT ![self] = l[self] + 1]
              /\ pc' = [pc EXCEPT ![self] = "lvl"]
              /\ UNCHANGED << level, last_to_enter >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << level, last_to_enter, l >>

exit(self) == /\ pc[self] = "exit"
              /\ level' = [level EXCEPT ![self] = -1]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED << last_to_enter, l >>

p(self) == ncs(self) \/ enter(self) \/ lvl(self) \/ last(self)
           \/ wait(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : p(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

=============================================================================