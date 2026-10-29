---------------------------- MODULE Session3Ext ----------------------------
(***************************************************************************)
(* A small extension of Session3 that adds two constant-valued operator    *)
(* definitions:                                                            *)
(*   - MinValue : a distinguished minimum integer value                    *)
(*   - NegFun   : a function from 1..3 into -3..-1                         *)
(* There are no variables, actions, temporal formulas, fairness            *)
(* conditions, assumptions, proofs or PlusCal code.                        *)
(***************************************************************************)
EXTENDS Session3, Integers

\* A distinguished minimum integer value.
MinValue == -3

\* A function from 1..3 to -3..-1, mapping each i to its negation.
NegFun == [i \in 1..3 |-> -i]

=============================================================================