---------------------------- MODULE LockHS ----------------------------
EXTENDS Integers, Stuttering

CONSTANT N
VARIABLE h_turn, s, turn, locked

TypeOKHS == (* type invariant *)
          /\ h_turn \in [1..N -> {1, 2}]
          /\ s \in {0, 1}
          /\ turn \in {1, 2}
          /\ locked \in {TRUE, FALSE}

InvHS == (* state invariant *)
        /\ TypeOKHS
        /\ (locked => turn = h_turn[1])
        /\ (s = 1 => turn = h_turn[2])

LockInv == (* lock invariant *)
           locked

SpecHS == (* next-state relation *)
         /\ locked' = IF locked THEN locked ELSE (turn = h_turn[1])
         /\ IF s = 0
             THEN turn' = IF turn = 1 THEN 2 ELSE 1
             ELSE turn' = turn
         /\ h_turn' = [h_turn EXCEPT ![1] = IF s = 0 THEN turn ELSE h_turn[1]]
         /\ s' = IF s = 0 THEN 1 ELSE 0

Spec == (* specification *)
       Init /\ [][Next]_<<h_turn, s, turn, locked>>

PSpec == (* Peterson specification with substitutions *)
        INSTANCE Peterson WITH
          <<x, y>> <- <<h_turn[1], h_turn[2]>>
          , p <- turn
          , q <- s

====================================