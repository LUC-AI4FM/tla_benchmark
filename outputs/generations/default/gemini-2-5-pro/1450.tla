---- MODULE SingleVariableSubset ----
EXTENDS Integers, TLC, Functions

(*
 This module specifies a single-variable system used to sample a random
 subset of the function set [S -> T]. The full function space has 10^9
 elements and should not be explicitly enumerated. The design instead
 initializes x to an element of RandomSubset(1000, [ S -> T ]).
*)

CONSTANTS S, T
ASSUME S = 1..9
ASSUME T = 1..10

VARIABLES x

F == [S -> T]
SubF == RandomSubset(1000, F)

Init == x \in SubF

Next == x' = x

Spec == Init /\ [][Next]_x

Inv == TRUE

================================