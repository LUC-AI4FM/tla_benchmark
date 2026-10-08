----------------------------- MODULE Rendezvous -----------------------------
EXTENDS Naturals, Sequences

CONSTANTS M, N

(*
  Basic sets and symbols
*)
NoOne == "None"
Red == "R"
Green == "G"
Blue == "B"
Colors == {Red, Green, Blue}
Agents == 1..M

(*
  State variables
*)
VARIABLES color, \* [agent -> color]
          active, \* [agent -> BOOLEAN], FALSE means faded/inactive
          met,    \* [agent -> Nat], per-agent meeting counter
          waiter, \* either NoOne or the single waiting agent
          totalMeet \* global number of completed pairwise meetings

vars == << color, active, met, waiter, totalMeet >>

(*
  Symmetric, deterministic local update for a meeting of two colors.
  Both participants update based only on the unordered pair of prior colors.
  Here we choose a canonical symmetric rule:
   - If colors are equal, both keep their color.
   - If colors differ, both become the unique third color.
*)
Third(c1, c2) ==
  CHOOSE x \in Colors: x # c1 /\ x # c2

Update(c1, c2) ==
  IF c1 = c2 THEN <<c1, c2>>
  ELSE <<Third(c1, c2), Third(c1, c2)>>

(*
  Initial condition
*)
Init ==
  /\ M \in Nat /\ M >= 1
  /\ N \in Nat /\ N >= 1
  /\ active = [i \in Agents |-> TRUE]
  /\ met    = [i \in Agents |-> 0]
  /\ color  \in [Agents -> Colors]
  /\ waiter = NoOne
  /\ totalMeet = 0

(*
  Actions
*)
ArriveWait(a) ==
  /\ a \in Agents
  /\ active[a]
  /\ waiter = NoOne
  /\ totalMeet < N
  /\ waiter' = a
  /\ UNCHANGED << color, active, met, totalMeet >>

Meet(a) ==
  /\ waiter \in Agents
  /\ a \in Agents
  /\ a # waiter
  /\ active[a]
  /\ active[waiter]
  /\ totalMeet < N
  /\ LET p == Update(color[waiter], color[a]) IN
     /\ color' = [color EXCEPT ![waiter] = p[1], ![a] = p[2]]
     /\ met'   = [met   EXCEPT ![waiter] = @ + 1, ![a] = @ + 1]
  /\ totalMeet' = totalMeet + 1
  /\ waiter' = NoOne
  /\ UNCHANGED active

FadeAfterBudget(a) ==
  /\ totalMeet = N
  /\ waiter = NoOne
  /\ a \in Agents
  /\ active[a]
  /\ active' = [active EXCEPT ![a] = FALSE]
  /\ UNCHANGED << color, met, waiter, totalMeet >>

Next ==
  \E a \in Agents:
      ArriveWait(a)
    \/ Meet(a)
    \/ FadeAfterBudget(a)

(*
  Accounting: sum of per-agent meeting counts
*)
RECURSIVE SumFrom(_)
SumFrom(i) ==
  IF i = 0 THEN 0 ELSE SumFrom(i-1) + met[i]

SumMet == SumFrom(M)

(*
  Type and safety/consistency invariants
   - Rendezvous holds at most one waiter (by type of 'waiter')
   - Global counter is bounded by N; increments only via Meet
   - Accounting: SumMet = 2 * totalMeet (each completed pair adds two)
   - After budget is exhausted, rendezvous remains empty (no new waiting)
*)
TypeOK ==
  /\ M \in Nat /\ M >= 1
  /\ N \in Nat /\ N >= 1
  /\ active \in [Agents -> BOOLEAN]
  /\ color  \in [Agents -> Colors]
  /\ met    \in [Agents -> Nat]
  /\ waiter \in Agents \cup {NoOne}
  /\ totalMeet \in 0..N
  /\ SumMet = 2 * totalMeet
  /\ (totalMeet = N => waiter = NoOne)

Spec ==
  Init /\ [][Next]_vars

=============================================================================