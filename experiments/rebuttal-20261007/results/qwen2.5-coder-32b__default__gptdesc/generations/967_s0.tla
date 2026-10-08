------------------------------- MODULE StoneCutting -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS W, N

VARIABLES pieces

Init == /\ pieces \in Seq(Naturals)
        /\ Len(pieces) = N
        /\ Sum(pieces) = W

Next ==
    LET nextPieces == Choose(s \in [1..N -> Naturals] : 
                                /\ Len(<<s[1], s[2] .. s[N]>>) = N
                                /\ Sum(<<s[1], s[2] .. s[N]>>) = W
                                /\ <<s[1], s[2] .. s[N]>> /= pieces)
    IN  \/ pieces' = nextPieces

Spec == Init /\ [][Next]_<<pieces>>

Invariants ==
    /\ \A target \in 1..W : 
        \E coeffs \in [1..N -> {-1, 0, 1}] :
            Sum(<<coeffs[1]*pieces[1], coeffs[2]*pieces[2] .. coeffs[N]*pieces[N]>>) = target

Fairness ==
    WF_next == WF_<<pieces>>(Next)

THEOREM Spec => []Invariants
=============================================================================