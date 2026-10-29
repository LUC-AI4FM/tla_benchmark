------------------------------ MODULE Session3Ext ------------------------------
(***************************************************************************)
(* A small extension module over Session3 with two constant-valued         *)
(* operator definitions:                                                   *)
(*   - MinInt : a distinguished minimum integer value                      *)
(*   - NegFun : a function from 1..3 to -3..-1                             *)
(* No variables, actions, temporal formulas, fairness conditions,          *)
(* assumptions or proofs are declared, as the description requires.       *)
(***************************************************************************)
EXTENDS Session3, Integers

\* A distinguished minimum integer value (32-bit signed minimum).
MinInt == -2147483648

\* A function from 1..3 into -3..-1, mapping each i to -i.
NegFun == [i \in 1..3 |-> -i]

================================================================================