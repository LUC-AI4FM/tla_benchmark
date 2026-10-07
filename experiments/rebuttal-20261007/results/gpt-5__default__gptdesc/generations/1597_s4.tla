------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(*
--algorithm FastME
variables x = 0, y = 0, b = [i \in 1..N |-> FALSE];

define
  Proc == 1..N;
end define;

process (P1 \in {1})
begin
Idle1:
  while TRUE do
    Try1:
      b[self] := TRUE;
      x := self;
      if y # 0 then
        b[self] := FALSE;
        await y = 0;
        goto Idle1;
      end if;
      y := self;
      if x # self then
        b[self] := FALSE;
        await \A j \in Proc \ {self}: ~b[j];
        if y # self then
          await y = 0;
          goto Idle1;
        end if;
      end if;
      CS1:
      skip;
      Exit1:
      y := 0;
      b[self] := FALSE;
  end while;
end process;

process (P2 \in 2..N)
begin
Idle2:
  while TRUE do
    Try2:
      b[self] := TRUE;
      x := self;
      if y # 0 then
        b[self] := FALSE;
        await y = 0;
        goto Idle2;
      end if;
      y := self;
      if x # self then
        b[self] := FALSE;
        await \A j \in Proc \ {self}: ~b[j];
        if y # self then
          await y = 0;
          goto Idle2;
        end if;
      end if;
      CS2:
      skip;
      Exit2:
      y := 0;
      b[self] := FALSE;
  end while;
end process;
end algorithm
*)

CONSTANTS

VARIABLES x, y, b, pc

Proc == 1..N
P1 == {1}
P2 == 2..N
Val == Proc \cup {0}

PCStates == {"idle", "checkY", "waitY0", "checkX", "awaitOthers", "checkY2", "cs"}

vars == << x, y, b, pc >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "idle"]

IdleToCheckY(i) ==
  /\ i \in Proc
  /\ pc[i] = "idle"
  /\ x' = i
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "checkY"]
  /\ UNCHANGED y

CheckY_YNotZero(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkY"
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitY0"]
  /\ UNCHANGED << x, y >>

WaitY0(i) ==
  /\ i \in Proc
  /\ pc[i] = "waitY0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED << x, y, b >>

CheckY_YZero(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkY"
  /\ y = 0
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "checkX"]
  /\ UNCHANGED << x, b >>

CheckX_XEqI(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkX"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b >>

CheckX_XNeqI(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkX"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "awaitOthers"]
  /\ UNCHANGED << x, y >>

AwaitOthers(i) ==
  /\ i \in Proc
  /\ pc[i] = "awaitOthers"
  /\ \A j \in Proc \ {i}: b[j] = FALSE
  /\ pc' = [pc EXCEPT ![i] = "checkY2"]
  /\ UNCHANGED << x, y, b >>

CheckY2_YEqI(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkY2"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b >>

CheckY2_YNeqI_Retry(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkY2"
  /\ y # i
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED << x, y, b >>

CS_Exit(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED x

ProcStep(i) ==
  IdleToCheckY(i)
  \/ CheckY_YNotZero(i)
  \/ WaitY0(i)
  \/ CheckY_YZero(i)
  \/ CheckX_XEqI(i)
  \/ CheckX_XNeqI(i)
  \/ AwaitOthers(i)
  \/ CheckY2_YEqI(i)
  \/ CheckY2_YNeqI_Retry(i)
  \/ CS_Exit(i)

Next ==
  \E i \in Proc: ProcStep(i)

TypeOK ==
  /\ x \in Val
  /\ y \in Val
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> PCStates]

CSSet == { i \in Proc : pc[i] = "cs" }

MutualExclusion ==
  Cardinality(CSSet) <= 1

Liveness ==
  []<>(\E i \in Proc: pc[i] = "cs")

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ProcStep(1))
  /\ \A i \in P2: WF_vars(ProcStep(i))

=============================================================================