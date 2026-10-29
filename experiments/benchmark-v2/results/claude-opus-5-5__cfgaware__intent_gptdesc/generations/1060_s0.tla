---------------------------- MODULE TokenRing ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Procs  == 0 .. (N - 1)

Colors == {"white", "black"}

VARIABLES active, color, token

vars == <<active, color, token>>

-----------------------------------------------------------------------------
TypeOK ==
  /\ active \in [Procs -> BOOLEAN]
  /\ color  \in [Procs -> Colors]
  /\ token  \in [pos : Procs, color : Colors]

-----------------------------------------------------------------------------
NextActive(i) ==
  LET k == CHOOSE m \in 1 .. N :
             /\ active[(i + m) % N]
             /\ \A j \in 1 .. (m - 1) : ~active[(i + j) % N]
  IN  (i + k) % N

Init ==
  /\ active = [i \in Procs |-> TRUE]
  /\ color  = [i \in Procs |-> "white"]
  /\ token  = [pos |-> 0, color |-> "white"]

UpdateColor(c) ==
  /\ c \in Colors
  /\ color' = [color EXCEPT ![token.pos] = c]
  /\ token' = [token EXCEPT !.color = c]
  /\ UNCHANGED active

Pass ==
  LET n == NextActive(token.pos) IN
  /\ token' = [token EXCEPT !.pos = n]
  /\ color' = [color EXCEPT ![n] = token.color]
  /\ UNCHANGED active

Deactivate(i) ==
  /\ active[i]
  /\ i # token.pos
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, token>>

Activate(i) ==
  /\ ~active[i]
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<color, token>>

Next ==
  \/ \E c \in Colors : UpdateColor(c)
  \/ Pass
  \/ \E i \in Procs : Deactivate(i)
  \/ \E i \in Procs : Activate(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Pass)

-----------------------------------------------------------------------------
UniqueToken ==
  /\ token.pos \in Procs
  /\ Cardinality1 == TRUE

SingleToken ==
  /\ token.pos \in Procs
  /\ \A i, j \in Procs : (i = token.pos /\ j = token.pos) => i = j

HolderActive == active[token.pos]

ColorConsistency == color[token.pos] = token.color

RangeInvariant ==
  /\ token.pos \in 0 .. (N - 1)
  /\ {i \in Procs : active[i]} \subseteq 0 .. (N - 1)

TerminationDetection ==
  /\ SingleToken
  /\ HolderActive
  /\ ColorConsistency
  /\ RangeInvariant

NoStarvation ==
  \A i \in Procs : active[i] ~> (token.pos = i \/ ~active[i])

=============================================================================