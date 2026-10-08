---------------------------- MODULE WeighingPieces ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT W, N

VARIABLE pieces

pieces == << >>
 
Init ==
  /\ pieces \in [1..W -> Nat]
  /\ Cardinality(pieces) = N
 
Next ==
  /\ Init
  /\ \E p \in [1..N -> {-1, 0, 1}] :
      /\ \A t \in 1..W :
          /\ \E coeffs \in [1..N -> {-1, 0, 1}] :
              Sum({coeffs[i] * pieces[i] : i \in 1..N}) = t
      /\ Sum(pieces) = W
 
Spec == Init /\ [][Next]_pieces

THEOREM Spec => []Cardinality(pieces) = N
THEOREM Spec => []Sum(pieces) = W
THEOREM Spec => []( \A t \in 1..W : 
                    \E coeffs \in [1..N -> {-1, 0, 1}] :
                        Sum({coeffs[i] * pieces[i] : i \in 1..N}) = t )
=============================================================================