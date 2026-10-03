------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals

CONSTANT N

(*
--algorithm FastME
variables x = 0, y = 0, b = [i \in 1..N |-> FALSE];

process Fast \in {1} fair
begin
ncs:    skip;
tryA:   b[1] := TRUE;
        x := 1;
tryB:   if y # 0 then
          b[1] := FALSE;
          await y = 0;
          goto tryA;
        else
          y := 1;
          goto checkX;
        end if;
checkX: if x # 1 then
          b[1] := FALSE;
          await \A j \in 2..N: ~b[j];
          goto recheckY;
        else
          goto cs;
        end if;
recheckY:
        if y # 1 then
          await y = 0;
          goto tryA;
        else
          goto cs;
        end if;
cs:     skip;
exit:   y := 0;
        b[1] := FALSE;
        goto ncs;
end process;

process Others \in 2..N fair
variable self \in 2..N;
begin
ncs:    skip;
tryA:   b[self] := TRUE;
        x := self;
tryB:   if y # 0 then
          b[self] := FALSE;
          await y = 0;
          goto tryA;
        else
          y := self;
          goto checkX;
        end if;
checkX: if x # self then
          b[self] := FALSE;
          await \A j \in 1..N: j # self => ~b[j];
          goto recheckY;
        else
          goto cs;
        end if;
recheckY:
        if y # self then
          await y = 0;
          goto tryA;
        else
          goto cs;
        end if;
cs:     skip;
exit:   y := 0;
        b[self] := FALSE;
        goto ncs;
end process;
*)
(***************************************************************************)
(* Hand-written TLA+ translation capturing the PlusCal algorithm above.    *)
(***************************************************************************)

Proc        == 1..N
Others      == 2..N

VARIABLES x, y, b, pc

vars == << x, y, b, pc >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [ i \in Proc |-> FALSE ]
  /\ pc = [ i \in Proc |-> "ncs" ]

P1Next ==
  \* Process 1 (the distinguished process)
  \/ /\ pc[1] = "ncs"
     /\ pc' = [pc EXCEPT ![1] = "tryA"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[1] = "tryA"
     /\ b' = [b EXCEPT ![1] = TRUE]
     /\ x' = 1
     /\ pc' = [pc EXCEPT ![1] = "tryB"]
     /\ UNCHANGED << y >>
  \/ /\ pc[1] = "tryB" /\ y # 0
     /\ b' = [b EXCEPT ![1] = FALSE]
     /\ pc' = [pc EXCEPT ![1] = "awaitY0"]
     /\ UNCHANGED << x, y >>
  \/ /\ pc[1] = "tryB" /\ y = 0
     /\ y' = 1
     /\ pc' = [pc EXCEPT ![1] = "checkX"]
     /\ UNCHANGED << x, b >>
  \/ /\ pc[1] = "awaitY0" /\ y = 0
     /\ pc' = [pc EXCEPT ![1] = "tryA"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[1] = "checkX" /\ x # 1
     /\ b' = [b EXCEPT ![1] = FALSE]
     /\ pc' = [pc EXCEPT ![1] = "waitOthers"]
     /\ UNCHANGED << x, y >>
  \/ /\ pc[1] = "checkX" /\ x = 1
     /\ pc' = [pc EXCEPT ![1] = "cs"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[1] = "waitOthers" /\ (\A j \in Others: ~b[j])
     /\ pc' = [pc EXCEPT ![1] = "recheckY"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[1] = "recheckY" /\ y = 1
     /\ pc' = [pc EXCEPT ![1] = "cs"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[1] = "recheckY" /\ y # 1
     /\ pc' = [pc EXCEPT ![1] = "awaitY0b"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[1] = "awaitY0b" /\ y = 0
     /\ pc' = [pc EXCEPT ![1] = "tryA"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[1] = "cs"
     /\ pc' = [pc EXCEPT ![1] = "exit"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[1] = "exit"
     /\ y' = 0
     /\ b' = [b EXCEPT ![1] = FALSE]
     /\ pc' = [pc EXCEPT ![1] = "ncs"]
     /\ UNCHANGED << x >>

P2Next(i) ==
  \* Process for each i in 2..N
  \/ /\ pc[i] = "ncs"
     /\ pc' = [pc EXCEPT ![i] = "tryA"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[i] = "tryA"
     /\ b' = [b EXCEPT ![i] = TRUE]
     /\ x' = i
     /\ pc' = [pc EXCEPT ![i] = "tryB"]
     /\ UNCHANGED << y >>
  \/ /\ pc[i] = "tryB" /\ y # 0
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ pc' = [pc EXCEPT ![i] = "awaitY0"]
     /\ UNCHANGED << x, y >>
  \/ /\ pc[i] = "tryB" /\ y = 0
     /\ y' = i
     /\ pc' = [pc EXCEPT ![i] = "checkX"]
     /\ UNCHANGED << x, b >>
  \/ /\ pc[i] = "awaitY0" /\ y = 0
     /\ pc' = [pc EXCEPT ![i] = "tryA"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[i] = "checkX" /\ x # i
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ pc' = [pc EXCEPT ![i] = "waitOthers"]
     /\ UNCHANGED << x, y >>
  \/ /\ pc[i] = "checkX" /\ x = i
     /\ pc' = [pc EXCEPT ![i] = "cs"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[i] = "waitOthers" /\ (\A j \in Proc: j # i => ~b[j])
     /\ pc' = [pc EXCEPT ![i] = "recheckY"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[i] = "recheckY" /\ y = i
     /\ pc' = [pc EXCEPT ![i] = "cs"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[i] = "recheckY" /\ y # i
     /\ pc' = [pc EXCEPT ![i] = "awaitY0b"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[i] = "awaitY0b" /\ y = 0
     /\ pc' = [pc EXCEPT ![i] = "tryA"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[i] = "cs"
     /\ pc' = [pc EXCEPT ![i] = "exit"]
     /\ UNCHANGED << x, y, b >>
  \/ /\ pc[i] = "exit"
     /\ y' = 0
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ pc' = [pc EXCEPT ![i] = "ncs"]
     /\ UNCHANGED << x >>

Next ==
  P1Next
  \/ (\E i \in Others: P2Next(i))

Fairness ==
  /\ WF_vars(P1Next)
  /\ \A i \in Others: WF_vars(P2Next(i))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
  \A i, j \in Proc: i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")

InfinitelyOftenCS ==
  []<>(\E i \in Proc: pc[i] = "cs")

=============================================================================