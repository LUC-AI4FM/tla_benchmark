----------------------------- MODULE RingTermination -----------------------------

EXTENDS Naturals

CONSTANTS
  N,
  MaxPending

ASSUME N \in Nat /\ N >= 1
ASSUME MaxPending \in Nat

Nodes == 0 .. (N - 1)
Colors == {"white", "black"}
Succ(i) == IF i = N - 1 THEN 0 ELSE i + 1

VARIABLES
  active,      \* [Nodes -> BOOLEAN]
  pending,     \* [Nodes -> 0..MaxPending]
  procColor,   \* [Nodes -> Colors]
  tokenPos,    \* \in Nodes
  tokenColor,  \* \in Colors
  flag         \* \in BOOLEAN

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ pending \in [Nodes -> 0..MaxPending]
  /\ procColor \in [Nodes -> Colors]
  /\ tokenPos \in Nodes
  /\ tokenColor \in Colors
  /\ flag \in BOOLEAN

Terminated ==
  /\ \A i \in Nodes: ~active[i]
  /\ \A i \in Nodes: pending[i] = 0

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ pending = [i \in Nodes |-> 0]
  /\ procColor = [i \in Nodes |-> "white"]
  /\ tokenPos = 0
  /\ tokenColor = "white"
  /\ flag \in {FALSE, TRUE}
  /\ flag => Terminated

Send(i, j) ==
  /\ i \in Nodes /\ j \in Nodes
  /\ active[i]
  /\ pending[j] < MaxPending
  /\ pending' = [pending EXCEPT ![j] = @ + 1]
  /\ procColor' = [procColor EXCEPT ![i] = IF j < i THEN "black" ELSE @]
  /\ UNCHANGED << active, tokenPos, tokenColor, flag >>

Receive(i) ==
  /\ i \in Nodes
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ UNCHANGED << procColor, tokenPos, tokenColor, flag >>

Deactivate(i) ==
  /\ i \in Nodes
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED << pending, procColor, tokenPos, tokenColor, flag >>

TokenPass(i) ==
  /\ i \in Nodes
  /\ tokenPos = i
  /\ tokenPos' = Succ(i)
  /\ tokenColor' = IF tokenColor = "black" \/ procColor[i] = "black" THEN "black" ELSE "white"
  /\ procColor' = [procColor EXCEPT ![i] = "white"]
  /\ UNCHANGED << active, pending, flag >>

Detect ==
  /\ tokenPos = 0
  /\ tokenColor = "white"
  /\ Terminated
  /\ ~flag
  /\ flag' = TRUE
  /\ UNCHANGED << active, pending, procColor, tokenPos, tokenColor >>

Next ==
  \/ \E i \in Nodes, j \in Nodes: Send(i, j)
  \/ \E i \in Nodes: Receive(i)
  \/ \E i \in Nodes: Deactivate(i)
  \/ \E i \in Nodes: TokenPass(i)
  \/ Detect

vars == << active, pending, procColor, tokenPos, tokenColor, flag >>

Fairness ==
  /\ \A i \in Nodes: WF_vars(TokenPass(i))
  /\ WF_vars(Detect)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

Safety ==
  [] (flag => Terminated)

Quiescence ==
  [] (Terminated => [] Terminated)

Liveness ==
  (Terminated ~> flag)

=============================================================================