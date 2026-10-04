---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

(*
--algorithm FastMutex
variables x = 0, y = 0, b = [i \in 1..N |-> FALSE];

fair process proc \in 1..N
variable j = 1;
begin
ncs: while TRUE do
        skip;
     l1: b[self] := TRUE;
     l2: x := self;
     l3: if y # 0 then
     l4:    b[self] := FALSE;
     l5:    await y = 0;
            goto l1;
         end if;
     l6: y := self;
     l7: if x # self then
     l8:    b[self] := FALSE;
            j := 1;
     l9:    while j <= N do
               await ~b[j];
               j := j + 1;
            end while;
     l10:   if y # self then
               await y = 0;
               goto l1;
            end if;
         end if;
     cs: skip;
     l11: y := 0;
     l12: b[self] := FALSE;
     end while;
end process;
end algorithm
*)

\* BEGIN TRANSLATION
VARIABLES x, y, b, pc, j

vars == << x, y, b, pc, j >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        (* Process proc *)
        /\ j = [self \in 1..N |-> 1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "l1"]
             /\ UNCHANGED << x, y, b, j >>

l1(self) == /\ pc[self] = "l1"
            /\ b' = [b EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << x, y, j >>

l2(self) == /\ pc[self] = "l2"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << y, b, j >>

l3(self) == /\ pc[self] = "l3"
            /\ IF y # 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "l4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, y, b, j >>

l4(self) == /\ pc[self] = "l4"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, y, j >>

l5(self) == /\ pc[self] = "l5"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << x, y, b, j >>

l6(self) == /\ pc[self] = "l6"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l7"]
            /\ UNCHANGED << x, b, j >>

l7(self) == /\ pc[self] = "l7"
            /\ IF x # self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j >>

l8(self) == /\ pc[self] = "l8"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l9"]
            /\ UNCHANGED << x, y >>

l9(self) == /\ pc[self] = "l9"
            /\ IF j[self] <= N
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l9"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l10"]
                       /\ j' = j
            /\ UNCHANGED << x, y, b >>

l10(self) == /\ pc[self] = "l10"
             /\ IF y # self
                   THEN /\ y = 0
                        /\ pc' = [pc EXCEPT ![self] = "l1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << x, y, b, j >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l11"]
            /\ UNCHANGED << x, y, b, j >>

l11(self) == /\ pc[self] = "l11"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l12"]
             /\ UNCHANGED << x, b, j >>

l12(self) == /\ pc[self] = "l12"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j >>

proc(self) == ncs(self) \/ l1(self) \/ l2(self) \/ l3(self) \/ l4(self)
                 \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self) \/ l9(self)
                 \/ l10(self) \/ cs(self) \/ l11(self) \/ l12(self)

Next == (\E self \in 1..N: proc(self))

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ \A self \in 1..N : WF_vars(proc(self))

\* END TRANSLATION

-----------------------------------------------------------------------------

(* Safety: Mutual Exclusion *)
Invariant == \A i, k \in 1..N : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

(* Liveness: If some process is perpetually outside ncs, then some process enters cs infinitely often *)
CondLiveness == (\E i \in 1..N : []<>(pc[i] # "ncs")) => (\E i \in 1..N : []<>(pc[i] = "cs"))

=============================================================================