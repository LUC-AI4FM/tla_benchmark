---------------------------- MODULE TrivialSystem ----------------------------
EXTENDS Integers

CONSTANT AlwaysTrue
VARIABLE x

Spec == x = 0 /\ [][x' = x]_x

THEOREM Spec => <>TRUE => <>[]TRUE
PROOF * Trivial system satisfies the temporal tautology *
  BY TLAPS
  P1: <>TRUE => <>[]TRUE DEF==
    <>TRUE => (<>TRUE => []<>TRUE) 
      BY propositional temporal logic
    == TRUE
  SHOW THEOREM BY P1

=============================================================================