---------------------------- MODULE MCSession4 ----------------------------
EXTENDS Session4, Integers

\* Distinguished minimum integer value used by the model checker
\* in place of an unbounded integer constant.
const_MinInt == -1000

\* Union of function sets: for each length l in 0..5, all functions
\* (tuples) from 1..l into the shifted range (l+1)..(2*l).
const_Tuples == UNION { [1..l -> (l+1)..(2*l)] : l \in 0..5 }

=============================================================================