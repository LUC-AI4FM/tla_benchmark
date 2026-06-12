MODULE OperatorTest

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS A, B, C

VARIABLES x, y, z

Init == TRUE

Next == TRUE

Spec == Init /\ []Next

\* Define custom operators
Plus(a, b) == a + b
Minus(a, b) == a - b
Times(a, b) == a * b
Divide(a, b) == a \div b
Modulo(a, b) == a % b
LessThan(a, b) == a < b
GreaterThan(a, b) == a > b
LessThanOrEqualTo(a, b) == a <= b
GreaterThanOrEqualTo(a, b) == a >= b
Equals(a, b) == a = b
NotEquals(a, b) == a # b
And(p, q) == p /\ q
Or(p, q) == p \/ q
Implies(p, q) == p => q
Equiv(p, q) == p <=> q
Not(p) == ~p
Union(S1, S2) == S1 \cup S2
Intersection(S1, S2) == S1 \cap S2
SetMinus(S1, S2) == S1 \ S2
Subseteq(S1, S2) == S1 \subseteq S2
ProperSubset(S1, S2) == S1 \subset S2
CartesianProduct(S1, S2) == [S1 -> S2]
Domain(f) == DOMAIN f
Range(f) == {f[x] : x \in DOMAIN f}
Inverse(f) == [x \in Range(f) |-> CHOOSE y \in DOMAIN f : f[y] = x]
SequenceConcat(s1, s2) == s1 \o s2
SequenceHead(s) == Head(s)
SequenceTail(s) == Tail(s)
SequenceAppend(s, e) == Append(s, e)

\* Use ASSUME to assert prefix form usage
ASSUME Plus(4, 6) = +(4, 6)
ASSUME Minus(10, 3) = -(10, 3)
ASSUME Times(5, 7) = *(5, 7)
ASSUME Divide(20, 4) = \(20, 4)
ASSUME Modulo(9, 4) = %(9, 4)
ASSUME LessThan(3, 5) = <(3, 5)
ASSUME GreaterThan(8, 6) = >(8, 6)
ASSUME LessThanOrEqualTo(7, 7) = <=(7, 7)
ASSUME GreaterThanOrEqualTo(10, 9) = >=(10, 9)
ASSUME Equals(2, 2) = =(2, 2)
ASSUME NotEquals(3, 4) = #\(3, 4)
ASSUME And(TRUE, FALSE) = /\/\(TRUE, FALSE)
ASSUME Or(TRUE, FALSE) = \/(TRUE, FALSE)
ASSUME Implies(FALSE, TRUE) = =>(FALSE, TRUE)
ASSUME Equiv(TRUE, TRUE) = <=>(TRUE, TRUE)
ASSUME Not(FALSE) = ~(FALSE)
ASSUME Union({1, 2}, {3}) = \cup({1, 2}, {3})
ASSUME Intersection({1, 2}, {2, 3}) = \cap({1, 2}, {2, 3})
ASSUME SetMinus({1, 2, 3}, {2}) = \( {1, 2, 3}, {2} )
ASSUME Subseteq({1, 2}, {1, 2, 3}) = \subseteq({1, 2}, {1, 2, 3})
ASSUME ProperSubset({1, 2}, {1, 2, 3}) = \subset({1, 2}, {1, 2, 3})
ASSUME CartesianProduct({1, 2}, {a, b}) = [ {1, 2} -> {a, b} ]
ASSUME SequenceConcat(<<1, 2>>, <<3>>) = \o(<<1, 2>>, <<3>>)
ASSUME SequenceHead(<<1, 2, 3>>) = Head(<<1, 2, 3>>)
ASSUME SequenceTail(<<1, 2, 3>>) = Tail(<<1, 2, 3>>)
ASSUME SequenceAppend(<<1, 2>>, 3) = Append(<<1, 2>>, 3)

\* Test built-in symbolic forms
ASSUME 1 \in {1, 2, 3}
ASSUME {1, 2} \cup {2, 3} = {1, 2, 3}
ASSUME {1, 2, 3} \ {2} = {1, 3}
ASSUME {1, 2} \subseteq {1, 2, 3}
ASSUME {1, 2} \subset {1, 2, 3}