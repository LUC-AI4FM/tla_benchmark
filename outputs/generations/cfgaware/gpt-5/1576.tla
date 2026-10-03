------------------------------ MODULE ConcurrentQueue ------------------------------

EXTENDS Naturals, Sequences

CONSTANTS N, Procs, Val

(*
--algorithm Queue
variables q = << >>, rV = [p \in Procs |-> "null"];
fair process (self \in Procs)
variable v;
begin
L0:
  while TRUE do
    either
      v := CHOOSE x \in Val: TRUE;
      if Len(q) < N then
        q := <<v>> \o q;
        rV[self] := "okay";
      else
        rV[self] := "full";
      end if;
    or
      v := CHOOSE x \in Val: TRUE;
      if Len(q) < N then
        q := Append(q, v);
        rV[self] := "okay";
      else
        rV[self] := "full";
      end if;
    or
      if q # << >> then
        rV[self] := q[1];
        q := Tail(q);
      else
        rV[self] := "empty";
      end if;
    or
      if q # << >> then
        rV[self] := q[Len(q)];
        q := SubSeq(q, 1, Len(q) - 1);
      else
        rV[self] := "empty";
      end if;
    end either;
  end while;
end process;
end algorithm;
*)

VARIABLES q, rV, pc

Res == Val \cup {"okay", "full", "empty", "null"}

TypeOK ==
  /\ q \in Seq(Val)
  /\ rV \in [Procs -> Res]
  /\ pc \in [Procs -> {0, 1}]

LenBound == Len(q) <= N

Init ==
  /\ q = << >>
  /\ rV = [p \in Procs |-> "null"]
  /\ pc = [p \in Procs |-> 0]
  /\ TypeOK
  /\ LenBound

EF_OK(p, v) ==
  /\ p \in Procs
  /\ v \in Val
  /\ Len(q) < N
  /\ q' = << v >> \o q
  /\ rV' = [rV EXCEPT ![p] = "okay"]
  /\ pc' = [pc EXCEPT ![p] = 1 - pc[p]]

EF_Full(p) ==
  /\ p \in Procs
  /\ Len(q) >= N
  /\ q' = q
  /\ rV' = [rV EXCEPT ![p] = "full"]
  /\ pc' = [pc EXCEPT ![p] = 1 - pc[p]]

EB_OK(p, v) ==
  /\ p \in Procs
  /\ v \in Val
  /\ Len(q) < N
  /\ q' = Append(q, v)
  /\ rV' = [rV EXCEPT ![p] = "okay"]
  /\ pc' = [pc EXCEPT ![p] = 1 - pc[p]]

EB_Full(p) ==
  /\ p \in Procs
  /\ Len(q) >= N
  /\ q' = q
  /\ rV' = [rV EXCEPT ![p] = "full"]
  /\ pc' = [pc EXCEPT ![p] = 1 - pc[p]]

DF_OK(p) ==
  /\ p \in Procs
  /\ Len(q) > 0
  /\ rV' = [rV EXCEPT ![p] = q[1]]
  /\ q' = Tail(q)
  /\ pc' = [pc EXCEPT ![p] = 1 - pc[p]]

DF_Empty(p) ==
  /\ p \in Procs
  /\ Len(q) = 0
  /\ q' = q
  /\ rV' = [rV EXCEPT ![p] = "empty"]
  /\ pc' = [pc EXCEPT ![p] = 1 - pc[p]]

DB_OK(p) ==
  /\ p \in Procs
  /\ Len(q) > 0
  /\ rV' = [rV EXCEPT ![p] = q[Len(q)]]
  /\ q' = SubSeq(q, 1, Len(q) - 1)
  /\ pc' = [pc EXCEPT ![p] = 1 - pc[p]]

DB_Empty(p) ==
  /\ p \in Procs
  /\ Len(q) = 0
  /\ q' = q
  /\ rV' = [rV EXCEPT ![p] = "empty"]
  /\ pc' = [pc EXCEPT ![p] = 1 - pc[p]]

P(p) ==
  \/ \E v \in Val: EF_OK(p, v)
  \/ EF_Full(p)
  \/ \E v \in Val: EB_OK(p, v)
  \/ EB_Full(p)
  \/ DF_OK(p)
  \/ DF_Empty(p)
  \/ DB_OK(p)
  \/ DB_Empty(p)

Next == \E p \in Procs: P(p)

vars == << q, rV, pc >>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Procs: WF_vars(P(p))
  /\ [] LenBound

=============================================================================