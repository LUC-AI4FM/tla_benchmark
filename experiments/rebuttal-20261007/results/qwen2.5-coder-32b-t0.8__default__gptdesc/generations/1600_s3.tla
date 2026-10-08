------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals, Sequences

CONSTANTS N

VARIABLES x, y, b, pc, j

Init == 
  /\ x = 0
  /\ y = 0
  /\ \A p \in 1..N : b[p] = FALSE
  /\ \A p \in 1..N : pc[p] = "start"
  /\ \A p \in 1..N : j[p] = 0

PAction ==
  \/ /\ \E p \in 1..N : pc[p] = "start" 
     /\ (pc' = [pc EXCEPT ![p] = "try"])
        /\ x' = x
        /\ y' = y
        /\ b' = b
        /\ j' = j
  \/ /\ \E p \in 1..N : pc[p] = "try"
     /\ LET r == (y + p) % N IN
     /\ (\A q \in 1..N : b[q] => (q <= r))
     /\ pc'[p] = IF /\ \A q \in 1..N : b[q] => (q <= r)
                  THEN "crit"
                  ELSE "backoff"
        /\ x' = x
        /\ y' = y
        /\ b'[p] = b[p] \/ [b EXCEPT ![p] = TRUE]
        /\ j'[p] = IF \A q \in 1..N : b[q] => (q <= r)
                   THEN j[p]
                   ELSE j[p] + 1
  \/ /\ \E p \in 1..N : pc[p] = "backoff"
     /\ LET r == (y + p) % N IN
     /\ (\A q \in 1..N : b[q] => (q <= r))
     /\ pc'[p] = IF (\A q \in 1..N : b[q] => (q <= r)) \/ j[p] > 2
                  THEN "try"
                  ELSE "wait"
        /\ x' = x
        /\ y' = y
        /\ b'[p] = [b EXCEPT ![p] = FALSE]
        /\ j'[p] = IF (\A q \in 1..N : b[q] => (q <= r)) \/ j[p] > 2
                   THEN 0
                   ELSE j[p]
  \/ /\ \E p \in 1..N : pc[p] = "wait"
     /\ pc'[p] = "try"
        /\ x' = x
        /\ y' = (y + 1) % N
        /\ b'[p] = b
        /\ j'[p] = j[p]
  \/ /\ \E p \in 1..N : pc[p] = "crit"
     /\ pc'[p] = "start"
        /\ x' = x
        /\ y' = y
        /\ b'[p] = [b EXCEPT ![p] = FALSE]
        /\ j'[p] = 0

Next == 
  \E p \in 1..N : (pc[p] # "done") => PAction

Spec ==
  WF_pc == \A p \in 1..N : <<p, "start">> \in WF
  WF_y == <<y>> \in WF
  Spec_0 ==
    /\ Init
    /\ [][Next]_<<pc, y>>
    /\ SF_\E p \in 1..N : <<p, "try">>

MutualExclusion ==
  \A p,q \in 1..N : 
     pc[p] = "crit" /\ pc[q] = "crit" => p = q

Liveness ==
  WF_y

THEOREM Spec_0 /\ MutualExclusion /\ Liveness

=============================================================================