----------------------------- MODULE FastLamport -----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

Proc == 1..N
Others == 2..N

(*
--algorithm FastME
variables x = 0, y = 0, b = [i \in Proc |-> TRUE], f = [i \in Proc |-> FALSE];

process (P1 = 1)
variable self \in {1};
begin
ncs:
  goto setX;

setX:
  x := self;
  goto checkY;

checkY:
  if y # 0 then
     f[self] := TRUE;
     goto waitY;
  else
     goto setY;
  end if;

waitY:
  await y = 0;
  f[self] := FALSE;
  goto setX;

setY:
  y := self;
  goto checkX;

checkX:
  if x = self then
     goto cs;
  else
     b[self] := FALSE;
     goto awaitB;
  end if;

awaitB:
  await \A j \in Proc : j = self \/ b[j];
  goto recheckY;

recheckY:
  if y = self then
     goto cs;
  else
     f[self] := TRUE;
     goto waitY;
  end if;

cs:
  skip;

exit:
  y := 0;
  b[self] := TRUE;
  f[self] := FALSE;
  goto ncs;
end process;

process (P \in 2..N)
variable self \in 2..N;
begin
ncs:
  goto setX;

setX:
  x := self;
  goto checkY;

checkY:
  if y # 0 then
     f[self] := TRUE;
     goto waitY;
  else
     goto setY;
  end if;

waitY:
  await y = 0;
  f[self] := FALSE;
  goto setX;

setY:
  y := self;
  goto checkX;

checkX:
  if x = self then
     goto cs;
  else
     b[self] := FALSE;
     goto awaitB;
  end if;

awaitB:
  await \A j \in Proc : j = self \/ b[j];
  goto recheckY;

recheckY:
  if y = self then
     goto cs;
  else
     f[self] := TRUE;
     goto waitY;
  end if;

cs:
  skip;

exit:
  y := 0;
  b[self] := TRUE;
  f[self] := FALSE;
  goto ncs;
end process;

end algorithm
*)

\* Generated (manually written) TLA+ translation

VARIABLES x, y, b, f, pc

PCSet == {"ncs","setX","checkY","waitY","setY","checkX","awaitB","recheckY","cs","exit"}

vars == << x, y, b, f, pc >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> TRUE]
  /\ f = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "ncs"]

TypeOK ==
  /\ x \in {0} \cup Proc
  /\ y \in {0} \cup Proc
  /\ b \in [Proc -> BOOLEAN]
  /\ f \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> PCSet]

A_ncs(p) ==
  /\ p \in Proc
  /\ pc[p] = "ncs"
  /\ pc' = [pc EXCEPT ![p] = "setX"]
  /\ UNCHANGED << x, y, b, f >>

A_setX(p) ==
  /\ p \in Proc
  /\ pc[p] = "setX"
  /\ x' = p
  /\ pc' = [pc EXCEPT ![p] = "checkY"]
  /\ UNCHANGED << y, b, f >>

A_checkY_wait(p) ==
  /\ p \in Proc
  /\ pc[p] = "checkY"
  /\ y # 0
  /\ f' = [f EXCEPT ![p] = TRUE]
  /\ pc' = [pc EXCEPT ![p] = "waitY"]
  /\ UNCHANGED << x, y, b >>

A_checkY_ok(p) ==
  /\ p \in Proc
  /\ pc[p] = "checkY"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![p] = "setY"]
  /\ UNCHANGED << x, y, b, f >>

A_waitY(p) ==
  /\ p \in Proc
  /\ pc[p] = "waitY"
  /\ y = 0
  /\ f' = [f EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "setX"]
  /\ UNCHANGED << x, y, b >>

A_setY(p) ==
  /\ p \in Proc
  /\ pc[p] = "setY"
  /\ y' = p
  /\ pc' = [pc EXCEPT ![p] = "checkX"]
  /\ UNCHANGED << x, b, f >>

A_checkX_fast(p) ==
  /\ p \in Proc
  /\ pc[p] = "checkX"
  /\ x = p
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED << x, y, b, f >>

A_checkX_slow(p) ==
  /\ p \in Proc
  /\ pc[p] = "checkX"
  /\ x # p
  /\ b' = [b EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "awaitB"]
  /\ UNCHANGED << x, y, f >>

A_awaitB(p) ==
  /\ p \in Proc
  /\ pc[p] = "awaitB"
  /\ \A j \in Proc : (j = p) \/ b[j]
  /\ pc' = [pc EXCEPT ![p] = "recheckY"]
  /\ UNCHANGED << x, y, b, f >>

A_recheckY_ok(p) ==
  /\ p \in Proc
  /\ pc[p] = "recheckY"
  /\ y = p
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED << x, y, b, f >>

A_recheckY_fail(p) ==
  /\ p \in Proc
  /\ pc[p] = "recheckY"
  /\ y # p
  /\ f' = [f EXCEPT ![p] = TRUE]
  /\ pc' = [pc EXCEPT ![p] = "waitY"]
  /\ UNCHANGED << x, y, b >>

A_cs(p) ==
  /\ p \in Proc
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "exit"]
  /\ UNCHANGED << x, y, b, f >>

A_exit(p) ==
  /\ p \in Proc
  /\ pc[p] = "exit"
  /\ y' = 0
  /\ b' = [b EXCEPT ![p] = TRUE]
  /\ f' = [f EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "ncs"]
  /\ UNCHANGED << x >>

ProcNext(p) ==
  A_ncs(p)
  \/ A_setX(p)
  \/ A_checkY_wait(p)
  \/ A_checkY_ok(p)
  \/ A_waitY(p)
  \/ A_setY(p)
  \/ A_checkX_fast(p)
  \/ A_checkX_slow(p)
  \/ A_awaitB(p)
  \/ A_recheckY_ok(p)
  \/ A_recheckY_fail(p)
  \/ A_cs(p)
  \/ A_exit(p)

P1Next == ProcNext(1)
POtherNext(i) == ProcNext(i)

Next ==
  P1Next
  \/ (\E i \in Others : POtherNext(i))

Spec ==
  Init /\ [][Next]_vars
  /\ WF_vars(P1Next)
  /\ \A i \in Others : WF_vars(POtherNext(i))

MutualExclusion ==
  \A p \in Proc : \A q \in Proc :
    (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

SomeCS == \E p \in Proc : pc[p] = "cs"

Liveness == []<>(SomeCS)

=============================================================================