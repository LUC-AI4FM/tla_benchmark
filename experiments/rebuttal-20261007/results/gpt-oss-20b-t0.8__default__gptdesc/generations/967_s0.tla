------------------------------ MODULE StoneCutting ------------------------------
EXTENDS Naturals, Sequences, TLC

(* CONSTANTS --------------------------------------------------------------- *)
CONSTANTS W, N          \* Total weight and number of pieces

(* VARIABLES --------------------------------------------------------------- *)
VARIABLE partition       \* Sequence of natural numbers representing the pieces

(* RECURSIVE DEFINITIONS --------------------------------------------------- *)
RECURSIVE Partitions/2
Partitions(n,w) ==
  IF n = 0 THEN
    IF w = 0 THEN {<>} ELSE {}
  ELSE
    { x~s | x \in Nat /\ x > 0 /\ s \in Partitions(n-1, w-x) }

RECURSIVE CoeffSeqs/1
CoeffSeqs(k) ==
  IF k = 0 THEN {<>}
  ELSE { c~cs | c \in {-1,0,1} /\ cs \in CoeffSeqs(k-1) }

RECURSIVE SumProd/2
SumProd(a,b) ==
  IF Len(a) = 0 THEN 0
  ELSE Head(a)*Head(b)+SumProd(Tail(a), Tail(b))

RECURSIVE SumRec/1
SumRec(s) ==
  IF s = <> THEN 0
  ELSE Head(s)+SumRec(Tail(s))

(* HELPERS --------------------------------------------------------------- *)
Balanced(p) == \A t \in 1..W :
                 \E c \in CoeffSeqs(N) : SumProd(p,c)=t

(* INITIAL STATE ----------------------------------------------------------- *)
Init ==
  partition \in Partitions(N,W)
  /\ Balanced(partition)

(* NEXT ACTION ------------------------------------------------------------- *)
Next ==
  \E p' \in Partitions(N,W) :
      (Balanced(p') /\ partition' = p')

(* SPECIFICATION ----------------------------------------------------------- *)
Spec == Init /\ [][Next]_partition

(* INVARIANTS -------------------------------------------------------------- *)
InvSum    == SumRec(partition) = W
InvPos    == \A i \in 1..N : ElemAt(partition,i) > 0

=============================================================================