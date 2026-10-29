---------------------------- MODULE Session3Ext ----------------------------
EXTENDS Session3, Integers

\* A distinguished minimum integer value.
MinInt == -2147483648

\* A function from 1..3 into -3..-1, mapping each element to its negation.
NegFun == [i \in 1..3 |-> -i]

=============================================================================