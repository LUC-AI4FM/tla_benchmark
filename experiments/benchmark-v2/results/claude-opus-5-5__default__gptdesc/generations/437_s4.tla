---------------------------- MODULE PrefixPostfixOps ----------------------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLES x, y

vars == <<x, y>>

-----------------------------------------------------------------------------
\* Higher-order operators that take a prefix or postfix operator as argument.

Pre(F(_), a)  == F(a)
Post(G(_), a) == G(a)
Twice(F(_), a) == F(F(a))

\* User-defined prefix and postfix operators.
-. a  == {a}
a ^+  == a \cup {1}
a ^*  == SUBSET a
a ^#  == Cardinality(a)

\* Definitions that use the built-in prefix and postfix operators syntactically.
PowerSet(S)    == Pre(SUBSET, S)
BigUnion(S)    == Pre(UNION, S)
Dom(f)         == Pre(DOMAIN, f)
Neg(b)         == Pre(~, b)
Single(a)      == Pre(-., a)
Closure(S)     == Post(^+, S)
Subsets(S)     == Post(^*, S)
Card(S)        == Post(^#, S)
PrimedX        == Post(', x)
PrimedY        == Post(', y)
YUnchanged     == Pre(UNCHANGED, y)
XUnchanged     == Pre(UNCHANGED, x)

-----------------------------------------------------------------------------
\* Tiny state machine over sets.

Init ==
    /\ x = {}
    /\ y = {1}

Grow ==
    /\ PrimedX = x \cup y
    /\ YUnchanged

Reset ==
    /\ PrimedX = {}
    /\ YUnchanged

Next == Grow \/ Reset

NextEnabled == Pre(ENABLED, Next)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Safety

TypeOK ==
    /\ x \in Pre(SUBSET, {1})
    /\ y = {1}

AlwaysEnabled == NextEnabled

\* Temporal property derived using [] and <> passed as operator arguments.
Property ==
    /\ Pre([], TypeOK)
    /\ Pre([], Pre(<>, x = y))

Liveness == Pre([], Pre(<>, x = y))

-----------------------------------------------------------------------------
\* Validation of expected parsing and evaluation behavior.

ASSUME
    /\ Print(<<"SUBSET", PowerSet({1, 2})>>, TRUE)
    /\ PowerSet({1, 2}) = {{}, {1}, {2}, {1, 2}}
    /\ Print(<<"UNION", BigUnion({{1}, {2}})>>, TRUE)
    /\ BigUnion({{1}, {2}}) = {1, 2}
    /\ Print(<<"DOMAIN", Dom(<<5, 6>>)>>, TRUE)
    /\ Dom(<<5, 6>>) = {1, 2}
    /\ Print(<<"~", Neg(FALSE)>>, TRUE)
    /\ Neg(FALSE)
    /\ Print(<<"-.", Single(3)>>, TRUE)
    /\ Single(3) = {3}
    /\ -. 4 = {4}
    /\ Print(<<"^+", Closure({2})>>, TRUE)
    /\ Closure({2}) = {1, 2}
    /\ {3}^+ = {1, 3}
    /\ Print(<<"^*", Subsets({1})>>, TRUE)
    /\ Subsets({1}) = {{}, {1}}
    /\ {2}^* = {{}, {2}}
    /\ Print(<<"^#", Card({1, 2})>>, TRUE)
    /\ Card({1, 2}) = 2
    /\ {1, 2, 3}^# = 3
    /\ Twice(SUBSET, {}) = {{}, {{}}}
    /\ Twice(UNION, {{{1}}}) = {1}
    /\ Twice(-., 0) = {{0}}

=============================================================================