---------------------------- MODULE ModCounter ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

VARIABLE x

vars == <<x>>

Values == 0..(N - 1)

(* Successor function on counter values *)
Succ(v) == (v + 1) % N

(* Iterated successor: Iter[k][v] is the value after k increments from v *)
Iter[k \in Nat] ==
    [v \in Values |-> IF k = 0 THEN v ELSE Succ(Iter[k - 1][v])]

-----------------------------------------------------------------------------
Init == x = 0

Increment == x' = Succ(x)

Next == Increment

Spec == Init /\ [][Next]_vars /\ SF_vars(Next)

-----------------------------------------------------------------------------
(* Safety: the counter always lies in 0..N-1 *)
TypeOK == x \in Values

Safety == []TypeOK

(* Determinism: from any state, exactly one successor value is possible,
   and the increment is always enabled. *)
Determinism ==
    /\ ENABLED Next
    /\ Cardinality({ y \in Values : y = Succ(x) }) = 1

DeterminismInv == Determinism

(* Periodicity: after N increments the counter returns to its value *)
Periodicity == Iter[N][x] = x

(* No earlier return is required, but v recurs within N steps *)
RecurWithinN == \E k \in 1..N : Iter[k][x] = x

(* Liveness: every value is visited infinitely often *)
VisitsInfinitelyOften(k) == []<>(x = k)

Liveness == \A k \in Values : []<>(x = k)

(* Recurrence: whenever x = v, x = v again later *)
Recurrence == \A v \in Values : (x = v) ~> (x = v)

(* Simple temporal assertion: eventually the counter equals k *)
EventuallyEquals(k) == <>(x = k)

AllEventually == \A k \in Values : <>(x = k)

-----------------------------------------------------------------------------
THEOREM Spec => Safety
THEOREM Spec => []DeterminismInv
THEOREM Spec => []Periodicity
THEOREM Spec => Liveness
=============================================================================