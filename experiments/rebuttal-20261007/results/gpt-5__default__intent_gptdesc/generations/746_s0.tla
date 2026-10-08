------------------------------ MODULE Rendezvous ------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
  M,                \* number of agents (positive integer)
  N,                \* global meeting budget (positive integer)
  Colors,           \* set of exactly three distinct colors
  ColorNext,        \* deterministic symmetric color-transition function
  Null              \* marker for empty rendezvous slot

(*
  Parameters and assumptions
*)
ASSUME
  /\ M \in Nat \ {0}
  /\ N \in Nat \ {0}
  /\ Cardinality(Colors) = 3
  /\ ColorNext \in [ (Colors \X Colors) -> Colors ]
  /\ \A c1, c2 \in Colors : ColorNext[<<c1, c2>>] = ColorNext[<<c2, c1>>]
  /\ Null \notin 1..M

(*
  Basic sets
*)
Agents == 1..M

(*
  State variables
    color[a]   = current color of agent a
    active[a]  = TRUE iff agent a is active (not faded)
    wait       = Null if rendezvous is empty; otherwise the unique waiting agent
    gCount     = global count of completed pairwise meetings (bounded by N)
    counts[a]  = number of meetings recorded by agent a
*)
VARIABLES color, active, wait, gCount, counts

vars == << color, active, wait, gCount, counts >>

(*
  Initialization
*)
Init ==
  /\ color \in [Agents -> Colors]
  /\ active = [a \in Agents |-> TRUE]
  /\ wait = Null
  /\ gCount = 0
  /\ counts = [a \in Agents |-> 0]

Empty == wait = Null

(*
  Actions
*)
Arrive(a) ==
  /\ a \in Agents
  /\ active[a]
  /\ Empty
  /\ gCount < N
  /\ wait' = a
  /\ UNCHANGED << color, gCount, counts, active >>

Meet(a, b) ==
  /\ a \in Agents /\ b \in Agents /\ a # b
  /\ wait = b
  /\ active[a] /\ active[b]
  /\ gCount < N
  /\ LET na == ColorNext[<< color[a], color[b] >>]
         nb == ColorNext[<< color[b], color[a] >>]
     IN
        /\ color'  = [color EXCEPT ![a] = na, ![b] = nb]
        /\ counts' = [counts EXCEPT ![a] = @ + 1, ![b] = @ + 1]
        /\ gCount' = gCount + 1
        /\ wait'   = Null
        /\ UNCHANGED active

FadeOnBudget(a) ==
  /\ a \in Agents
  /\ active[a]
  /\ gCount = N
  /\ active' = [active EXCEPT ![a] = FALSE]
  /\ UNCHANGED << color, wait, gCount, counts >>

Next ==
  \/ \E a \in Agents : Arrive(a)
  \/ \E a \in Agents : \E b \in Agents : Meet(a, b)
  \/ \E a \in Agents : FadeOnBudget(a)

Spec ==
  Init /\ [][Next]_vars

(*
  Derived quantities and invariants/properties (to be checked against Spec)
*)
TotalRecorded == Sum({ counts[a] : a \in Agents })

TypeInv ==
  /\ color \in [Agents -> Colors]
  /\ active \in [Agents -> BOOLEAN]
  /\ wait \in (Agents \cup {Null})
  /\ gCount \in 0..N
  /\ counts \in [Agents -> Nat]

RendezvousExclusive ==
  [] (wait = Null \/ (\E a \in Agents : wait = a))

CounterBound ==
  [] (gCount \in 0..N)

CounterMonotone ==
  [] (gCount' >= gCount)

CounterOnlyOnMeeting ==
  [] ( (gCount' > gCount)
       =>
       \E a, b \in Agents :
         /\ a # b
         /\ counts' = [i \in Agents |-> IF i = a \/ i = b THEN counts[i] + 1 ELSE counts[i]]
         /\ color'  = [i \in Agents |-> IF i = a THEN ColorNext[<< color[a], color[b] >>]
                                     ELSE IF i = b THEN ColorNext[<< color[b], color[a] >>]
                                     ELSE color[i]]
         /\ wait' = Null )

LocalUpdateOnMeeting ==
  [] ( (gCount' = gCount + 1)
       =>
       \E a, b \in Agents :
         /\ a # b
         /\ counts' = [i \in Agents |-> IF i = a \/ i = b THEN counts[i] + 1 ELSE counts[i]]
         /\ color'  = [i \in Agents |-> IF i = a THEN ColorNext[<< color[a], color[b] >>]
                                     ELSE IF i = b THEN ColorNext[<< color[b], color[a] >>]
                                     ELSE color[i]]
         /\ wait' = Null )

NoCountingAfterBudget ==
  [] (gCount = N => gCount' = N)

AccountingAlways ==
  [] (TotalRecorded = 2 * gCount)

AccountingAtBudget ==
  [] (gCount = N => TotalRecorded = 2 * N)

TerminationConsistency ==
  [] (gCount = N => [] (gCount = N))

=============================================================================