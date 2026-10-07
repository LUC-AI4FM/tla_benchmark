----------------------------- MODULE FastLamportFastMutex -----------------------------

EXTENDS Naturals, Integers, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(*
--algorithm FastMutex
variables x = 0, y = 0, b = [i \in 1..N |-> FALSE];

process Dist \in {1}
variable self = 1;
begin
Loop:
  while TRUE do
  ncs:
    b[self] := TRUE;
    x := self;
    if y # 0 then
      b[self] := FALSE;
      await y = 0;
      goto ncs;
    end if;
    y := self;
    if x # self then
      b[self] := FALSE;
      await \A j \in 1..N: (j = self) \/ ~b[j];
      if y # self then
        await y = 0;
        goto ncs;
      end if;
    end if;
  cs:
    skip; \* critical section
    y := 0;
    b[self] := FALSE;
    goto ncs;
  end while;
end process;

process Other \in 2..N
variable self \in 2..N;
begin
Loop:
  while TRUE do
  ncs:
    b[self] := TRUE;
    x := self;
    if y # 0 then
      b[self] := FALSE;
      await y = 0;
      goto ncs;
    end if;
    y := self;
    if x # self then
      b[self] := FALSE;
      await \A j \in 1..N: (j = self) \/ ~b[j];
      if y # self then
        await y = 0;
        goto ncs;
      end if;
    end if;
  cs:
    skip; \* critical section
    y := 0;
    b[self] := FALSE;
    goto ncs;
  end while;
end process;

end algorithm
*)

Proc == 1..N
Dist == {1}
Others == 2..N

PCStates == {"idle","setx","testy","waity1","sety","testx","waitb","checky2","waity2","cs"}

VARIABLES x, y, b, pc

vars == << x, y, b, pc >>

TypeOK ==
  /\ x \in Proc \cup {0}
  /\ y \in Proc \cup {0}
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> PCStates]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "idle"]

ProcStep(p) ==
  /\ p \in Proc
  /\ \/
     /\ pc[p] = "idle"
     /\ b' = [b EXCEPT ![p] = TRUE]
     /\ UNCHANGED << x, y >>
     /\ pc' = [pc EXCEPT ![p] = "setx"]
  \/
     /\ pc[p] = "setx"
     /\ x' = p
     /\ UNCHANGED << y, b >>
     /\ pc' = [pc EXCEPT ![p] = "testy"]
  \/
     /\ pc[p] = "testy" /\ y # 0
     /\ b' = [b EXCEPT ![p] = FALSE]
     /\ UNCHANGED << x, y >>
     /\ pc' = [pc EXCEPT ![p] = "waity1"]
  \/
     /\ pc[p] = "waity1" /\ y = 0
     /\ UNCHANGED << x, y, b >>
     /\ pc' = [pc EXCEPT ![p] = "idle"]
  \/
     /\ pc[p] = "testy" /\ y = 0
     /\ UNCHANGED << x, y, b >>
     /\ pc' = [pc EXCEPT ![p] = "sety"]
  \/
     /\ pc[p] = "sety"
     /\ y' = p
     /\ UNCHANGED << x, b >>
     /\ pc' = [pc EXCEPT ![p] = "testx"]
  \/
     /\ pc[p] = "testx" /\ x # p
     /\ b' = [b EXCEPT ![p] = FALSE]
     /\ UNCHANGED << x, y >>
     /\ pc' = [pc EXCEPT ![p] = "waitb"]
  \/
     /\ pc[p] = "testx" /\ x = p
     /\ UNCHANGED << x, y, b >>
     /\ pc' = [pc EXCEPT ![p] = "cs"]
  \/
     /\ pc[p] = "waitb" /\ \A j \in Proc: (j = p) \/ ~b[j]
     /\ UNCHANGED << x, y, b >>
     /\ pc' = [pc EXCEPT ![p] = "checky2"]
  \/
     /\ pc[p] = "checky2" /\ y = p
     /\ UNCHANGED << x, y, b >>
     /\ pc' = [pc EXCEPT ![p] = "cs"]
  \/
     /\ pc[p] = "checky2" /\ y # p
     /\ UNCHANGED << x, y, b >>
     /\ pc' = [pc EXCEPT ![p] = "waity2"]
  \/
     /\ pc[p] = "waity2" /\ y = 0
     /\ UNCHANGED << x, y, b >>
     /\ pc' = [pc EXCEPT ![p] = "idle"]
  \/
     /\ pc[p] = "cs"
     /\ y' = 0
     /\ b' = [b EXCEPT ![p] = FALSE]
     /\ UNCHANGED x
     /\ pc' = [pc EXCEPT ![p] = "idle"]

Next ==
  \E p \in Proc: ProcStep(p)

MutualExclusion ==
  \A p, q \in Proc: (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

LiveCS ==
  []<>(\E p \in Proc: pc[p] = "cs")

DistFair == WF_vars(ProcStep(1))

OthersFairEach == \A p \in Others: WF_vars(ProcStep(p))

Spec ==
  Init /\ [][Next]_vars /\ DistFair /\ OthersFairEach

================================================================================