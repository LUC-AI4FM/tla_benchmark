------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME /\ N \in Nat /\ N >= 1
       /\ M \in Nat /\ 1 <= M /\ M <= N

(*
PlusCal model with two process declarations (syntactically distinct groups).
Both groups execute identical Lamport's fast mutual exclusion logic.

--algorithm FastMutexAlg
variables flag = [i \in 1..N |-> FALSE], x = 0, y = 0;

fair process GroupA \in 1..M
begin
StartA:
  goto SetFlagA;
SetFlagA:
  flag[self] := TRUE;
  x := self;
CheckYA:
  if (y # 0) then
    flag[self] := FALSE;
Backoff1A:
    await y = 0;
    goto SetFlagA;
  end if;
  y := self;
CheckXA:
  if (x # self) then
    flag[self] := FALSE;
WaitFlagsA:
    await \A k \in { i \in 1..N : i # self }: flag[k] = FALSE;
RecheckYA:
    if (y # self) then
      await y = 0;
      goto SetFlagA;
    end if;
  end if;
CSA:
  skip;
ExitYA:
  y := 0;
ClearFlagA:
  flag[self] := FALSE;
RemainderA:
  goto SetFlagA;
end process;

fair process GroupB \in M+1..N
begin
StartB:
  goto SetFlagB;
SetFlagB:
  flag[self] := TRUE;
  x := self;
CheckYB:
  if (y # 0) then
    flag[self] := FALSE;
Backoff1B:
    await y = 0;
    goto SetFlagB;
  end if;
  y := self;
CheckXB:
  if (x # self) then
    flag[self] := FALSE;
WaitFlagsB:
    await \A k \in { i \in 1..N : i # self }: flag[k] = FALSE;
RecheckYB:
    if (y # self) then
      await y = 0;
      goto SetFlagB;
    end if;
  end if;
CSB:
  skip;
ExitYB:
  y := 0;
ClearFlagB:
  flag[self] := FALSE;
RemainderB:
  goto SetFlagB;
end process;
end algorithm
*)

(***************************************************************************)
(* TLA+ specification corresponding to the above algorithm                 *)
(***************************************************************************)

Proc == 1..N
GroupA == 1..M
GroupB == IF M < N THEN (M+1)..N ELSE {}

VARIABLES pc, flag, x, y

vars == << pc, flag, x, y >>

Init ==
  /\ pc = [ i \in Proc |-> "start" ]
  /\ flag = [ i \in Proc |-> FALSE ]
  /\ x = 0
  /\ y = 0

A_Start(i) ==
  /\ pc[i] = "start"
  /\ pc' = [pc EXCEPT ![i] = "SetFlag"]
  /\ UNCHANGED << flag, x, y >>

A_SetFlag(i) ==
  /\ pc[i] = "SetFlag"
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "SetX"]
  /\ UNCHANGED << x, y >>

A_SetX(i) ==
  /\ pc[i] = "SetX"
  /\ x' = i
  /\ pc' = [pc EXCEPT ![i] = "CheckY"]
  /\ UNCHANGED << flag, y >>

A_CheckY_Backoff(i) ==
  /\ pc[i] = "CheckY"
  /\ y # 0
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "Backoff1"]
  /\ UNCHANGED << x, y >>

A_CheckY_Forward(i) ==
  /\ pc[i] = "CheckY"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "SetY"]
  /\ UNCHANGED << flag, x, y >>

A_Backoff1(i) ==
  /\ pc[i] = "Backoff1"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "SetFlag"]
  /\ UNCHANGED << flag, x, y >>

A_SetY(i) ==
  /\ pc[i] = "SetY"
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "CheckX"]
  /\ UNCHANGED << flag, x >>

A_CheckX_SlowPath(i) ==
  /\ pc[i] = "CheckX"
  /\ x # i
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "WaitFlags"]
  /\ UNCHANGED << x, y >>

A_CheckX_FastPath(i) ==
  /\ pc[i] = "CheckX"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << flag, x, y >>

A_WaitFlags(i) ==
  /\ pc[i] = "WaitFlags"
  /\ \A k \in (Proc \ {i}) : flag[k] = FALSE
  /\ pc' = [pc EXCEPT ![i] = "RecheckY"]
  /\ UNCHANGED << flag, x, y >>

A_RecheckY_Enter(i) ==
  /\ pc[i] = "RecheckY"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << flag, x, y >>

A_RecheckY_Retry(i) ==
  /\ pc[i] = "RecheckY"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "SetFlag"]
  /\ UNCHANGED << flag, x, y >>

A_CS(i) ==
  /\ pc[i] = "CS"
  /\ pc' = [pc EXCEPT ![i] = "ExitY"]
  /\ UNCHANGED << flag, x, y >>

A_ExitY(i) ==
  /\ pc[i] = "ExitY"
  /\ y' = 0
  /\ pc' = [pc EXCEPT ![i] = "ClearFlag"]
  /\ UNCHANGED << flag, x >>

A_ClearFlag(i) ==
  /\ pc[i] = "ClearFlag"
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "Remainder"]
  /\ UNCHANGED << x, y >>

A_Remainder(i) ==
  /\ pc[i] = "Remainder"
  /\ pc' = [pc EXCEPT ![i] = "SetFlag"]
  /\ UNCHANGED << flag, x, y >>

ProcNext(i) ==
    A_Start(i)
  \/ A_SetFlag(i)
  \/ A_SetX(i)
  \/ A_CheckY_Backoff(i)
  \/ A_CheckY_Forward(i)
  \/ A_Backoff1(i)
  \/ A_SetY(i)
  \/ A_CheckX_SlowPath(i)
  \/ A_CheckX_FastPath(i)
  \/ A_WaitFlags(i)
  \/ A_RecheckY_Enter(i)
  \/ A_RecheckY_Retry(i)
  \/ A_CS(i)
  \/ A_ExitY(i)
  \/ A_ClearFlag(i)
  \/ A_Remainder(i)

Next == \E i \in Proc : ProcNext(i)

Spec == Init /\ [][Next]_vars /\ \A i \in Proc : WF_vars(ProcNext(i))

IsInCS(i) == pc[i] = "CS"

CSSet == { i \in Proc : IsInCS(i) }

Invariant == Cardinality(CSSet) <= 1

Liveness == []<>(\E i \in Proc : IsInCS(i))

=============================================================================