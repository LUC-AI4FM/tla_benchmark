---- MODULE FastMutex ----
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat \A N >= 2

(*
--algorithm FastMutex
variables x = 0, y = 0, b = [i \in 1..N |-> FALSE], fail = [i \in 1..N |-> FALSE];

process (P1 = 1)
begin
P1_Try:
  while TRUE do
    P1_Ready: await ~fail[self];
    P1_Claim: b[self] := TRUE; x := self;
    if y # 0 then
      P1_Backoff:
        b[self] := FALSE;
        await y = 0;
        goto P1_Claim;
    else
      P1_SetY: y := self;
      if x # self then
        P1_WaitOthers:
          b[self] := FALSE;
          await \A i \in 1..N: i = self \/ ~b[i];
          if y # self then
            P1_WaitY0:
              await y = 0;
              goto P1_Claim;
          end if;
      end if;
      P1_CS: skip; \* critical section
      P1_Exit:
        y := 0;
        b[self] := FALSE;
    end if;
  end while;
end process;

process (P \in 2..N)
begin
P_Try:
  while TRUE do
    P_Ready: await ~fail[self];
    P_Claim: b[self] := TRUE; x := self;
    if y # 0 then
      P_Backoff:
        b[self] := FALSE;
        await y = 0;
        goto P_Claim;
    else
      P_SetY: y := self;
      if x # self then
        P_WaitOthers:
          b[self] := FALSE;
          await \A i \in 1..N: i = self \/ ~b[i];
          if y # self then
            P_WaitY0:
              await y = 0;
              goto P_Claim;
          end if;
      end if;
      P_CS: skip; \* critical section
      P_Exit:
        y := 0;
        b[self] := FALSE;
    end if;
  end while;
end process;
end algorithm;
*)

Proc == 1..N

VARIABLES x, y, b, pc, fail

vars == << x, y, b, pc, fail >>

Labels == {"try","checkY","waitY0","checkX","waitB","checkYAgain","cs","exit"}

TypeOK ==
  /\ x \in ({0} \cup Proc)
  /\ y \in ({0} \cup Proc)
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> Labels]
  /\ fail \in [Proc -> BOOLEAN]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "try"]
  /\ fail = [i \in Proc |-> FALSE]

Try(p) ==
  /\ p \in Proc
  /\ pc[p] = "try"
  /\ ~fail[p]
  /\ x' = p
  /\ b' = [b EXCEPT ![p] = TRUE]
  /\ pc' = [pc EXCEPT ![p] = "checkY"]
  /\ UNCHANGED << y, fail >>

CheckY(p) ==
  /\ p \in Proc
  /\ pc[p] = "checkY"
  /\ ( /\ y # 0
       /\ b' = [b EXCEPT ![p] = FALSE]
       /\ pc' = [pc EXCEPT ![p] = "waitY0"]
       /\ UNCHANGED << x, y, fail >>
     \/ /\ y = 0
        /\ y' = p
        /\ pc' = [pc EXCEPT ![p] = "checkX"]
        /\ UNCHANGED << x, b, fail >> )

WaitY0(p) ==
  /\ p \in Proc
  /\ pc[p] = "waitY0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![p] = "try"]
  /\ UNCHANGED << x, y, b, fail >>

CheckX(p) ==
  /\ p \in Proc
  /\ pc[p] = "checkX"
  /\ ( /\ x # p
       /\ b' = [b EXCEPT ![p] = FALSE]
       /\ pc' = [pc EXCEPT ![p] = "waitB"]
       /\ UNCHANGED << x, y, fail >>
     \/ /\ x = p
        /\ pc' = [pc EXCEPT ![p] = "cs"]
        /\ UNCHANGED << x, y, b, fail >> )

WaitB(p) ==
  /\ p \in Proc
  /\ pc[p] = "waitB"
  /\ \A i \in Proc: (i = p) \/ ~b[i]
  /\ pc' = [pc EXCEPT ![p] = "checkYAgain"]
  /\ UNCHANGED << x, y, b, fail >>

CheckYAgain(p) ==
  /\ p \in Proc
  /\ pc[p] = "checkYAgain"
  /\ ( /\ y # p
       /\ pc' = [pc EXCEPT ![p] = "waitY0"]
       /\ UNCHANGED << x, y, b, fail >>
     \/ /\ y = p
        /\ pc' = [pc EXCEPT ![p] = "cs"]
        /\ UNCHANGED << x, y, b, fail >> )

CS(p) ==
  /\ p \in Proc
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "exit"]
  /\ UNCHANGED << x, y, b, fail >>

Exit(p) ==
  /\ p \in Proc
  /\ pc[p] = "exit"
  /\ y' = 0
  /\ b' = [b EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "try"]
  /\ UNCHANGED << x, fail >>

Act(p) ==
  Try(p) \/ CheckY(p) \/ WaitY0(p) \/ CheckX(p) \/ WaitB(p) \/ CheckYAgain(p) \/ CS(p) \/ Exit(p)

Next ==
  \E p \in Proc: Act(p)

Proc1Next == Act(1)

OthersNext ==
  \E p \in 2..N: Act(p)

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Proc1Next) /\ WF_vars(OthersNext)

MutualExclusion ==
  \A i, j \in Proc: i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")

InfinitelyOftenCS ==
  []<>(\E p \in Proc: pc[p] = "cs")

Safety == MutualExclusion

Liveness == InfinitelyOftenCS

====