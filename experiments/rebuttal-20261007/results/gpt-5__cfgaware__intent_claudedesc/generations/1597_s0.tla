------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals, Integers

(*
PlusCal sketch (not used semantically here) to illustrate two syntactically distinct process groups:
--algorithm Fast
variables x = 0, y = 0, b = [i \in 1..N |-> FALSE];

process (Leader = 1)
begin LeaderLoop:
  A1: b[1] := TRUE;
  A2: x := 1;
  A3: if y # 0 then
        Backoff1: b[1] := FALSE;
        WaitY01: await y = 0;
        goto A1;
      else
        SetY1: y := 1;
        CheckX1: if x # 1 then
                   SlowClr1: b[1] := FALSE;
                   WaitAll1: await \A j \in 1..N: (j = 1) \/ ~b[j];
                   CheckY1: if y # 1 then
                              WaitY01: await y = 0;
                              goto A1;
                            end if;
                 end if;
        CS1: skip;
        ExitY01: y := 0;
        ExitClrB1: b[1] := FALSE;
        goto A1;
      end if;
end process;

process (Others \in 2..N)
begin OthersLoop:
  B1: b[self] := TRUE;
  B2: x := self;
  B3: if y # 0 then
        Backoff2: b[self] := FALSE;
        WaitY02: await y = 0;
        goto B1;
      else
        SetY2: y := self;
        CheckX2: if x # self then
                   SlowClr2: b[self] := FALSE;
                   WaitAll2: await \A j \in 1..N: (j = self) \/ ~b[j];
                   CheckY2: if y # self then
                              WaitY02: await y = 0;
                              goto B1;
                            end if;
                 end if;
        CS2: skip;
        ExitY02: y := 0;
        ExitClrB2: b[self] := FALSE;
        goto B1;
      end if;
end process;
end algorithm
*)

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES x, y, b, pc

ProcSet == 1..N

vars == << x, y, b, pc >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in ProcSet |-> FALSE]
  /\ pc = [i \in ProcSet |-> "A1"]

InCS(i) == pc[i] = "CS"

A1(i) ==
  /\ pc[i] = "A1"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "A2"]
  /\ UNCHANGED << x, y >>

A2(i) ==
  /\ pc[i] = "A2"
  /\ x' = i
  /\ pc' = [pc EXCEPT ![i] = "CheckY"]
  /\ UNCHANGED << y, b >>

CheckY(i) ==
  /\ pc[i] = "CheckY"
  /\ IF y # 0
        THEN /\ pc' = [pc EXCEPT ![i] = "BackoffClearB"]
             /\ UNCHANGED << x, y, b >>
        ELSE /\ pc' = [pc EXCEPT ![i] = "SetY"]
             /\ UNCHANGED << x, y, b >>

BackoffClearB(i) ==
  /\ pc[i] = "BackoffClearB"
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "WaitY0"]
  /\ UNCHANGED << x, y >>

WaitY0(i) ==
  /\ pc[i] = "WaitY0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "A1"]
  /\ UNCHANGED << x, y, b >>

SetY(i) ==
  /\ pc[i] = "SetY"
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "CheckX"]
  /\ UNCHANGED << x, b >>

CheckX(i) ==
  /\ pc[i] = "CheckX"
  /\ IF x # i
        THEN /\ pc' = [pc EXCEPT ![i] = "SlowClearB"]
             /\ UNCHANGED << x, y, b >>
        ELSE /\ pc' = [pc EXCEPT ![i] = "CS"]
             /\ UNCHANGED << x, y, b >>

SlowClearB(i) ==
  /\ pc[i] = "SlowClearB"
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "WaitFlags"]
  /\ UNCHANGED << x, y >>

WaitFlags(i) ==
  /\ pc[i] = "WaitFlags"
  /\ \A j \in ProcSet: (j = i) \/ ~b[j]
  /\ pc' = [pc EXCEPT ![i] = "CheckYeqI"]
  /\ UNCHANGED << x, y, b >>

CheckYeqI(i) ==
  /\ pc[i] = "CheckYeqI"
  /\ IF y = i
        THEN /\ pc' = [pc EXCEPT ![i] = "CS"]
             /\ UNCHANGED << x, y, b >>
        ELSE /\ pc' = [pc EXCEPT ![i] = "WaitY0"]
             /\ UNCHANGED << x, y, b >>

CS_step(i) ==
  /\ pc[i] = "CS"
  /\ pc' = [pc EXCEPT ![i] = "ExitY0"]
  /\ UNCHANGED << x, y, b >>

ExitY0(i) ==
  /\ pc[i] = "ExitY0"
  /\ y' = 0
  /\ pc' = [pc EXCEPT ![i] = "ExitClearB"]
  /\ UNCHANGED << x, b >>

ExitClearB(i) ==
  /\ pc[i] = "ExitClearB"
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "A1"]
  /\ UNCHANGED << x, y >>

PNext(i) ==
  A1(i) \/ A2(i) \/ CheckY(i) \/ BackoffClearB(i) \/ WaitY0(i)
  \/ SetY(i) \/ CheckX(i) \/ SlowClearB(i) \/ WaitFlags(i)
  \/ CheckYeqI(i) \/ CS_step(i) \/ ExitY0(i) \/ ExitClearB(i)

Next ==
  \E i \in ProcSet: PNext(i)

Fairness ==
  \A i \in ProcSet: WF_vars(PNext(i))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

Invariant ==
  \A i, j \in ProcSet: (i # j) => ~(InCS(i) /\ InCS(j))

Liveness ==
  []<>(\E i \in ProcSet: InCS(i))

==============================