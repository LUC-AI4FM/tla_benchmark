---------------------------- MODULE MC ----------------------------
EXTENDS Session3proj, TLC

\* Model-checking companion module for Session3proj.
\* It defines no variables, actions, temporal formulas or fairness.
\* Init, Next, Spec and any invariants or properties come from
\* Session3proj and are referenced from the TLC model configuration.
\* Defining them here would clash with the names in Session3proj.

\* First fixed integer set: a concrete domain for a model constant.
const_1 == {1, 2, 3}

\* Second fixed integer set: a concrete parameter set for a model constant.
const_2 == {0, 1, 2, 3, 4}

=============================================================================