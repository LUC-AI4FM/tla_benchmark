--------------------------- MODULE PetersonN ---------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANT N

ASSUME N \in Nat \ {0}

Procs == 1..N

(* --algorithm Peterson {
     variables level = [p \in Procs |-> -1],
               last_to_enter = [k \in 0..(N-2) |-> 1];

     process (proc \in Procs)
       variable l = 0;
     {
       p0: while (TRUE) {
             ncs: skip;
                  l := 0;
             p1:  while (l < N - 1) {
                    p2: level[self] := l;
                    p3: last_to_enter[l] := self;
                    p4: await (last_to_enter[l] # self)
                              \/ (\A k \in Procs \ {self} : level[k] < l);
                        l := l + 1;
                  };
             cs:  skip;
             p5:  level[self] := -1;
           }
     }
   }
*)
\* BEGIN TRANSLATION
VARIABLES level, last_to_enter, pc, l

vars == << level, last_to_enter, pc, l >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ level = [p \in Procs |-> -1]
        /\ last_to_enter = [k \in 0..(N-2) |-> 1]
        (* Process proc *)
        /\ l = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "p0"]

p0(self) == /\ pc[self] = "p0"
            /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ UNCHANGED << level, last_to_enter, l >>

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ l' = [l EXCEPT ![self] = 0]
             /\ pc' = [pc EXCEPT ![self] = "p1"]
             /\ UNCHANGED << level, last_to_enter >>

p1(self) == /\ pc[self] = "p1"
            /\ IF l[self] < N - 1
                  THEN /\ pc' = [pc EXCEPT ![self] = "p2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << level, last_to_enter, l >>

p2(self) == /\ pc[self] = "p2"
            /\ level' = [level EXCEPT ![self] = l[self]]
            /\ pc' = [pc EXCEPT ![self] = "p3"]
            /\ UNCHANGED << last_to_enter, l >>

p3(self) == /\ pc[self] = "p3"
            /\ last_to_enter' = [last_to_enter EXCEPT ![l[self]] = self]
            /\ pc' = [pc EXCEPT ![self] = "p4"]
            /\ UNCHANGED << level, l >>

p4(self) == /\ pc[self] = "p4"
            /\ \/ last_to_enter[l[self]] # self
               \/ \A k \in Procs \ {self} : level[k] < l[self]
            /\ l' = [l EXCEPT ![self] = l[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << level, last_to_enter >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ UNCHANGED << level, last_to_enter, l >>

p5(self) == /\ pc[self] = "p5"
            /\ level' = [level EXCEPT ![self] = -1]
            /\ pc' = [pc EXCEPT ![self] = "p0"]
            /\ UNCHANGED << last_to_enter, l >>

proc(self) == p0(self) \/ ncs(self) \/ p1(self) \/ p2(self)
                 \/ p3(self) \/ p4(self) \/ cs(self) \/ p5(self)

Next == (\E self \in Procs : proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

(* Auxiliary definitions (not part of Spec; no fairness or liveness asserted) *)
TypeOK == /\ level \in [Procs -> -1..(N-1)]
          /\ last_to_enter \in [0..(N-2) -> Procs]
          /\ l \in [Procs -> 0..(N-1)]
          /\ pc \in [Procs -> {"p0", "ncs", "p1", "p2", "p3", "p4", "cs", "p5"}]

MutualExclusion == \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

=============================================================================