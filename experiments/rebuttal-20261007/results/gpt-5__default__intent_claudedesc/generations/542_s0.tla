----------------------------- MODULE ConcurrentIncrement -----------------------------

EXTENDS Naturals

CONSTANTS Proc

ASSUME Proc = {1, 2}

VARIABLES x, done

vars == << x, done >>

Init ==
  /\ x = 0
  /\ done = [p \in Proc |-> FALSE]

Inc(p) ==
  /\ p \in Proc
  /\ ~done[p]
  /\ x' = x + 1
  /\ done' = [done EXCEPT ![p] = TRUE]

Next ==
  ∃ p \in Proc: Inc(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Inc(1))
  /\ WF_vars(Inc(2))

Termination ==
  <> (∀ p \in Proc: done[p])

=============================================================================