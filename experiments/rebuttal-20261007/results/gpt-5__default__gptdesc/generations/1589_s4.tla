----------------------------- MODULE Euclid -----------------------------
EXTENDS Naturals, Integers, TLC

(*
Euclid's algorithm (PlusCal)

--algorithm Euclid
variables 
  u_ini \in 1..MaxNum,
  v_ini \in 1..MaxNum,
  u = u_ini,
  v = v_ini;
begin
  Loop:
  while (u # v) do
    if (u > v) then
      DecU: u := u - v;
    else
      DecV: v := v - u;
    end if;
  end while;
  Done: skip;
end algorithm;
*)

CONSTANT MaxNum

ASSUME MaxNum \in Nat \ {0}

RECURSIVE GCDRec(_, _)
GCDRec(a, b) == IF b = 0 THEN a ELSE GCDRec(b, a % b)
GCD(a, b) == GCDRec(Abs(a), Abs(b))

VARIABLES pc, u_ini, v_ini, u, v, stepCnt, decUCount, decVCount

vars == << pc, u_ini, v_ini, u, v, stepCnt, decUCount, decVCount >>

Init ==
  /\ pc = "Loop"
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u = u_ini
  /\ v = v_ini
  /\ stepCnt = 0
  /\ decUCount = 0
  /\ decVCount = 0

Terminated == pc = "Done"

DecUAct ==
  /\ pc = "Loop"
  /\ u # v
  /\ u > v
  /\ u' = u - v
  /\ v' = v
  /\ stepCnt' = stepCnt + 1
  /\ decUCount' = decUCount + 1
  /\ decVCount' = decVCount
  /\ pc' = "Loop"
  /\ UNCHANGED << u_ini, v_ini >>

DecVAct ==
  /\ pc = "Loop"
  /\ u # v
  /\ v > u
  /\ v' = v - u
  /\ u' = u
  /\ stepCnt' = stepCnt + 1
  /\ decVCount' = decVCount + 1
  /\ decUCount' = decUCount
  /\ pc' = "Loop"
  /\ UNCHANGED << u_ini, v_ini >>

DoneAct ==
  /\ pc = "Loop"
  /\ u = v
  /\ pc' = "Done"
  /\ UNCHANGED << u, v, u_ini, v_ini, stepCnt, decUCount, decVCount >>

StutterAct ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == DecUAct \/ DecVAct \/ DoneAct \/ StutterAct

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeInv ==
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u \in 1..MaxNum
  /\ v \in 1..MaxNum
  /\ stepCnt \in Nat
  /\ decUCount \in Nat
  /\ decVCount \in Nat

NonZeroInv == /\ u >= 1 /\ v >= 1

GCDInv == GCD(u, v) = GCD(u_ini, v_ini)

CountersInv == stepCnt = decUCount + decVCount

CorrectnessInv ==
  Terminated => /\ u = v /\ u = GCD(u_ini, v_ini)

Inv == TypeInv /\ NonZeroInv /\ GCDInv /\ CountersInv /\ CorrectnessInv

Termination == <>Terminated
============================================================================