---------------------------- MODULE Peterson ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Procs == 1..N

(* --algorithm Peterson
variables level = [p \in Procs |-> 0],
          last_to_enter = [l \in 1..(N-1) |-> 1];

process proc \in Procs
variable lv = 0;
begin
ncs:   while TRUE do
         skip;
enter:   lv := 1;
loop:    while lv < N do
           level[self] := lv;
setlast:   last_to_enter[lv] := self;
wait:      await \/ last_to_enter[lv] # self
                 \/ \A k \in Procs \ {self} : level[k] < lv;
           lv := lv + 1;
         end while;
cs:      skip;
leave:   level[self] := 0;
       end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES level, last_to_enter, pc, lv

vars == << level, last_to_enter, pc, lv >>

ProcSet == Procs

Init == /\ level = [p \in Procs |-> 0]
        /\ last_to_enter = [l \in 1..(N-1) |-> 1]
        /\ lv = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "enter"]
             /\ UNCHANGED << level, last_to_enter, lv >>

enter(self) == /\ pc[self] = "enter"
               /\ lv' = [lv EXCEPT ![self] = 1]
               /\ pc' = [pc EXCEPT ![self] = "loop"]
               /\ UNCHANGED << level, last_to_enter >>

loop(self) == /\ pc[self] = "loop"
              /\ IF lv[self] < N
                    THEN /\ level' = [level EXCEPT ![self] = lv[self]]
                         /\ pc' = [pc EXCEPT ![self] = "setlast"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                         /\ level' = level
              /\ UNCHANGED << last_to_enter, lv >>

setlast(self) == /\ pc[self] = "setlast"
                 /\ last_to_enter' = [last_to_enter EXCEPT ![lv[self]] = self]
                 /\ pc' = [pc EXCEPT ![self] = "wait"]
                 /\ UNCHANGED << level, lv >>

wait(self) == /\ pc[self] = "wait"
              /\ \/ last_to_enter[lv[self]] # self
                 \/ \A k \in Procs \ {self} : level[k] < lv[self]
              /\ lv' = [lv EXCEPT ![self] = lv[self] + 1]
              /\ pc' = [pc EXCEPT ![self] = "loop"]
              /\ UNCHANGED << level, last_to_enter >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "leave"]
            /\ UNCHANGED << level, last_to_enter, lv >>

leave(self) == /\ pc[self] = "leave"
               /\ level' = [level EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self] = "ncs"]
               /\ UNCHANGED << last_to_enter, lv >>

proc(self) == ncs(self) \/ enter(self) \/ loop(self) \/ setlast(self)
                 \/ wait(self) \/ cs(self) \/ leave(self)

Next == (\E self \in Procs : proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

MutualExclusion == \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

=============================================================================