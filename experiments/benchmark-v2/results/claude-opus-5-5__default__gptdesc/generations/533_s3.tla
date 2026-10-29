------------------------------- MODULE MCSession4 -------------------------------
EXTENDS Session4, Integers

\* Distinguished minimum integer value, used as a model-checking helper constant.
MCMinValue == -1000

\* Union of function sets: for each l in 0..5, all functions (tuples) from 1..l
\* into the shifted range (l+1)..(2*l).
MCTupleSet == UNION { [1..l -> (l+1)..(2*l)] : l \in 0..5 }

=================================================================================