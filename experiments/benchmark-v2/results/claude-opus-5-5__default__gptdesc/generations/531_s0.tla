---------------------------- MODULE MC ----------------------------
EXTENDS Session3proj, TLC

\* Model-checking companion module for Session3proj.
\* It only supplies concrete integer sets to be substituted for
\* constants of the underlying specification when running TLC.

\* CONSTANT definitions @modelParameterConstants:0
const_1 ==
    {1, 2, 3}

\* CONSTANT definitions @modelParameterConstants:1
const_2 ==
    {0, 1, 2, 3, 4}

=============================================================================