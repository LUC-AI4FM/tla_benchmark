------------------------------ MODULE SharedRing ------------------------------

EXTENDS Naturals

CONSTANT N

(*
Processes are indexed 0..N-1 in a ring.
Each process i owns a shared register reg[i] and a private local register local[i].
pc[i] tracks the local control state of process i.
*)

Proc == 0 .. (N-1)

VARIABLES pc, reg, local

vars == << pc, reg, local >>

(*
Shared register states:
  "Stable0" : stably holds 0
  "Writing" : in transition 0 -> 1 (regular: reads may see 0 or 1)
  "Stable1" : stably holds 1
Process control states:
  "start"   : before starting the write
  "writing" : begun the write
  "written" : completed the write
  "done"    : finished the read
*)

Init ==
  /\ pc = [i \in Proc |-> "start"]
  /\ reg = [i \in Proc |-> "Stable0"]
  /\ local = [i \in Proc |-> "Undef"]

Left(i) == IF i = 0 THEN N - 1 ELSE i - 1

ReadVal(j) ==
  IF reg[j] = "Stable0" THEN {0}
  ELSE IF reg[j] = "Stable1" THEN {1}
  ELSE {0, 1}

Begin(i) ==
  /\ i \in Proc
  /\ pc[i] = "start"
  /\ reg[i] = "Stable0"
  /\ pc' = [pc EXCEPT ![i] = "writing"]
  /\ reg' = [reg EXCEPT ![i] = "Writing"]
  /\ UNCHANGED local

EndWrite(i) ==
  /\ i \in Proc
  /\ pc[i] = "writing"
  /\ reg[i] = "Writing"
  /\ pc' = [pc EXCEPT ![i] = "written"]
  /\ reg' = [reg EXCEPT ![i] = "Stable1"]
  /\ UNCHANGED local

Read(i) ==
  /\ i \in Proc
  /\ pc[i] = "written"
  /\ pc' = [pc EXCEPT ![i] = "done"]
  /\ local' = [local EXCEPT ![i] \in ReadVal(Left(i))]
  /\ UNCHANGED reg

Next ==
  \E i \in Proc : Begin(i) \/ EndWrite(i) \/ Read(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Proc : WF_vars(Begin(i))
  /\ \A i \in Proc : WF_vars(EndWrite(i))
  /\ \A i \in Proc : WF_vars(Read(i))

AllFinished == \A i \in Proc : pc[i] = "done"
AllZeroLocal == \A i \in Proc : local[i] = 0

TypeOK ==
  /\ pc \in [Proc -> {"start", "writing", "written", "done"}]
  /\ reg \in [Proc -> {"Stable0", "Writing", "Stable1"}]
  /\ local \in [Proc -> {"Undef", 0, 1}]
  /\ \A i \in Proc :
        /\ (pc[i] = "start") => reg[i] = "Stable0"
        /\ (pc[i] = "writing") => reg[i] = "Writing"
        /\ (pc[i] \in {"written", "done"}) => reg[i] = "Stable1"
        /\ (pc[i] = "done") => local[i] \in {0, 1}

Inv ==
  /\ TypeOK
  /\ ~(AllFinished /\ AllZeroLocal)

PCorrect ==
  [] (AllFinished => (\E i \in Proc : local[i] = 1))

=============================================================================