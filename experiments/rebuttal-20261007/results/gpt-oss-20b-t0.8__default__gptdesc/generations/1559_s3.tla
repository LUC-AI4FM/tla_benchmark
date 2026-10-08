MODULE LockProtocol
EXTENDS Naturals, Sequences

CONSTANTS Proc

VARIABLES f, turn, s, h

Init ==
    /\ f = [p \in Proc |-> FALSE]
    /\ turn = CHOOSE p \in Proc: TRUE
    /\ s = 0
    /\ h = <<>>

Phase0(p) ==
    /\ s = 0
    /\ f[p] = FALSE
    /\ f' = [f EXCEPT ![p] = TRUE]
    /\ turn' = turn
    /\ s' = 1
    /\ h' = h

Phase1(p) ==
    /\ s = 1
    /\ f' = f
    /\ turn' = CHOOSE q \in Proc: (q /= p)
    /\ s' = 2
    /\ h' = Append(h, turn')

Phase2(p) ==
    /\ s = 2
    /\ f' = f
    /\ turn' = turn
    /\ s' = 0
    /\ h' = h

Release(p) ==
    /\ s = 0
    /\ f[p] = TRUE
    /\ f' = [f EXCEPT ![p] = FALSE]
    /\ turn' = turn
    /\ s' = 0
    /\ h' = h

Next == \E p \in Proc : Phase0(p) \/ Phase1(p) \/ Phase2(p) \/ Release(p)

Spec == Init /\ [] [][Next]_<<f,turn,s,h>>