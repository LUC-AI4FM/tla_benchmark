------------------------------ MODULE TokenRingColors ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,          \* ring size
    Colors      \* finite set of colors (strings), e.g. {"red", "green", "blue"}

ASSUME NAssumption      == N \in Nat /\ N >= 1
ASSUME ColorsAssumption == Colors # {} /\ IsFiniteSet(Colors)

Proc == 0..(N - 1)

VARIABLES
    active,     \* set of currently active processes
    color,      \* color[p] : local color of process p
    token       \* [pos |-> holder index, color |-> token color]

vars == <<active, color, token>>

-----------------------------------------------------------------------------
\* Helpers

\* The next process clockwise from i (excluding i itself, unless only i
\* qualifies) that belongs to the set S. Requires S # {}.
Succ(i, S) ==
    LET d == CHOOSE k \in 1..N :
                /\ ((i + k) % N) \in S
                /\ \A j \in 1..(k - 1) : ((i + j) % N) \notin S
    IN (i + d) % N

Holder == token.pos

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ active \in (SUBSET Proc) \ {{}}
    /\ color \in [Proc -> Colors]
    /\ \E p \in active :
          token = [pos |-> p, color |-> color[p]]

-----------------------------------------------------------------------------
\* Actions

\* The token holder updates its local color; the token color is
\* synchronized with the new local color (update rule).
Recolor(c) ==
    /\ c \in Colors
    /\ color' = [color EXCEPT ![Holder] = c]
    /\ token' = [token EXCEPT !.color = c]
    /\ UNCHANGED active

\* The token holder forwards the token to its next active successor
\* (inactive processes are skipped but remain in the ring).
Pass ==
    /\ token' = [pos |-> Succ(Holder, active), color |-> token.color]
    /\ UNCHANGED <<active, color>>

\* The token holder forwards the token and becomes inactive.
\* Only allowed if some other process remains active to receive the token.
PassAndDeactivate ==
    /\ active \ {Holder} # {}
    /\ active' = active \ {Holder}
    /\ token' = [pos |-> Succ(Holder, active \ {Holder}), color |-> token.color]
    /\ UNCHANGED color

\* An inactive process is reactivated (it rejoins the token circulation).
Reactivate(p) ==
    /\ p \in Proc \ active
    /\ active' = active \cup {p}
    /\ UNCHANGED <<color, token>>

Next ==
    \/ \E c \in Colors : Recolor(c)
    \/ Pass
    \/ PassAndDeactivate
    \/ \E p \in Proc : Reactivate(p)

Fairness == WF_vars(Pass)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

TypeOK ==
    /\ active \subseteq Proc
    /\ color \in [Proc -> Colors]
    /\ token \in [pos : Proc, color : Colors]

\* At most one token; its position refers to exactly one process.
UniqueToken ==
    /\ token.pos \in Proc
    /\ Cardinality({p \in Proc : p = token.pos}) = 1

\* Only active processes hold the token.
HolderIsActive == token.pos \in active

\* Active set and token position are within 0..N-1.
RangeInvariant ==
    /\ \A p \in active : p \in 0..(N - 1)
    /\ token.pos \in 0..(N - 1)
    /\ active # {}

\* Consistency of token color (action property):
\*  - a local color changes only at the token holder, and the token
\*    color is synchronized with that new local color;
\*  - when the token moves, its color is carried unchanged.
ColorConsistency ==
    [][ /\ \A p \in Proc :
             color'[p] # color[p] =>
                 /\ p = token.pos
                 /\ token'.pos = token.pos
                 /\ token'.color = color'[p]
        /\ (token'.color # token.color) =>
                 /\ token'.pos = token.pos
                 /\ color'[token.pos] = token'.color
        /\ (token'.pos # token.pos) => token'.color = token.color
      ]_vars

\* Only the token holder may deactivate itself.
DeactivationByHolderOnly ==
    [][ \A p \in Proc : (p \in active /\ p \notin active') => p = token.pos ]_vars

Invariants ==
    /\ TypeOK
    /\ UniqueToken
    /\ HolderIsActive
    /\ RangeInvariant

-----------------------------------------------------------------------------
\* Liveness: no active process is permanently starved.

NoStarvation ==
    \A p \in Proc : (p \in active) ~> (token.pos = p)

-----------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => ColorConsistency
THEOREM Spec => DeactivationByHolderOnly
THEOREM Spec => NoStarvation
=============================================================================