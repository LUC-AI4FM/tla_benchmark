MODULE RingAlgorithm
EXTENDS Naturals

CONSTANT N \in Nat \ {0}

VARIABLES x, y, pc

vars == <<x, y, pc>>

Indices == 1..N
Left(i) == IF i = 1 THEN N ELSE i-1

(* --*--
algorithm Ring {
  const N;
  var x[1..N], y[1..N];
  variable pc[1..N];

  init:
    for i \in 1..N do
      x[i] := 0;
      y[i] := 0;
      pc[i] := "Init";
    end;

  next:
    choose i in 1..N with pc[i]="Init" then
      x[i] := 1;
      pc[i] := "Copy";

    or choose i in 1..N with pc[i]="Copy" then
      y[i] := x[Left(i)];
      pc[i] := "Done";
}
--*--) *)

Init ==
  /\ ∀ i ∈ Indices : (x[i] = 0) /\ (y[i] = 0) /\ (pc[i] = "Init")

SetX(i) == 
  /\ pc[i] = "Init"
  /\ x' = [x EXCEPT ![i] = 1]
  /\ pc' = [pc EXCEPT ![i] = "Copy"]
  /\ y' = y

CopyY(i) ==
  /\ pc[i] = "Copy"
  /\ y' = [y EXCEPT ![i] = x[Left(i)]]
  /\ pc' = [pc EXCEPT ![i] = "Done"]
  /\ x' = x

Next == ∃ i ∈ Indices : (SetX(i) \/