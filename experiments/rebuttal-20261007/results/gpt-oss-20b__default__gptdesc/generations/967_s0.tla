MODULE StoneCutting
EXTENDS Naturals, Sequences, TLC

CONSTANTS W, N

VARIABLES pieces

vars == <<pieces>>

(* Operators *)

SumSeq(seq) == \SUM i \in 1..Len(seq) : seq[i]

Partition(n,w) ==
    { seq \in Seq(Nat) : Len(seq)=n /\ SumSeq(seq)=w }

CoeffSet ==
    { coeff \in Seq({-1,0,1}) : Len(coeff)=N }

SumWeighted(coeffs,pieces) == \SUM i \in 1..Len(coeffs) : coeffs[i] * pieces[i]

Balanced(pieces,t) ==
    \E coeffs \in CoeffSet : SumWeighted(coeffs,pieces)=t

BalancedAll(pieces) ==
    \A t \in 1..W : Balanced(pieces, t)

Invariant(pieces) == SumSeq(pieces)=W /\ BalancedAll(pieces)

(* Initial state *)

Init == pieces \in Partition(N,W) /\ Invariant(pieces) /\ PrintT("Solution:", pieces)

(* Next action: stay in same state (no change) *)
Next == pieces' = pieces

Spec == Init /\ [][Next]_vars
===============================================================================