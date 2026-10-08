----------------------------- MODULE DiningPhilosophersCM -----------------------------
EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(*
  Chandy-Misra Dining Philosophers specification.

  Philosophers are numbered 0..N-1 in a ring.
  Fork f is the one between philosophers f and (f+1) % N.
*)

P == 0..(N-1)
Forks == 0..(N-1)

Succ(i) == (i + 1) % N
Prev(i) == (i + N - 1) % N

Left(f)  == f
Right(f) == Succ(f)

Endpoints(f) == {Left(f), Right(f)}
ForksOf(p) == {Prev(p), p}

Other(f, p) == IF p = Left(f) THEN Right(f) ELSE Left(f)

States == {"Thinking", "Hungry", "Eating"}

VARIABLES
  status,   \* [p \in P -> States]
  owner,    \* [f \in Forks -> P], must be in Endpoints(f)
  clean,    \* [f \in Forks -> BOOLEAN], TRUE = clean, FALSE = dirty
  request   \* [f \in Forks -> ({"None"} \cup P)], if in P then is the non-owner endpoint

vars == << status, owner, clean, request >>

Init ==
  /\ status = [p \in P |-> "Thinking"]
  /\ owner  = [f \in Forks |-> Left(f)]
  /\ clean  = [f \in Forks |-> FALSE]
  /\ request = [f \in Forks |-> "None"]

(*
  Local actions for philosopher p
*)

DecideHungry(p) ==
  /\ p \in P
  /\ status[p] = "Thinking"
  /\ status' = [status EXCEPT ![p] = "Hungry"]
  /\ UNCHANGED << owner, clean, request >>

StartEat(p) ==
  LET l == Prev(p) IN
  LET r == p IN
  /\ p \in P
  /\ status[p] = "Hungry"
  /\ owner[l] = p /\ owner[r] = p
  /\ clean[l] /\ clean[r]
  /\ status' = [status EXCEPT ![p] = "Eating"]
  /\ UNCHANGED << owner, clean, request >>

FinishEat(p) ==
  LET l == Prev(p) IN
  LET r == p IN
  /\ p \in P
  /\ status[p] = "Eating"
  /\ status' = [status EXCEPT ![p] = "Thinking"]
  /\ clean' = [clean EXCEPT ![l] = FALSE, ![r] = FALSE]
  /\ UNCHANGED << owner, request >>

MakeRequest(p, f) ==
  /\ p \in P /\ f \in ForksOf(p)
  /\ status[p] = "Hungry"
  /\ owner[f] # p
  /\ request[f] = "None"
  /\ request' = [request EXCEPT ![f] = p]
  /\ UNCHANGED << status, owner, clean >>

WithdrawRequest(p, f) ==
  /\ p \in P /\ f \in ForksOf(p)
  /\ status[p] = "Thinking"
  /\ request[f] = p
  /\ request' = [request EXCEPT ![f] = "None"]
  /\ UNCHANGED << status, owner, clean >>

ServeRequest(p, f) ==
  /\ p \in P /\ f \in Forks
  /\ owner[f] = p
  /\ request[f] \in Endpoints(f) \ { p }
  /\ status[p] # "Eating"
  /\ (status[p] # "Hungry" \/ ~clean[f])
     \* If thinking, pass immediately; if hungry, pass only if fork is dirty.
  /\ owner' = [owner EXCEPT ![f] = request[f]]
  /\ clean' = [clean EXCEPT ![f] = TRUE] \* Clean before/when passing.
  /\ request' = [request EXCEPT ![f] = "None"]
  /\ UNCHANGED status

NextP(p) ==
  \/ DecideHungry(p)
  \/ StartEat(p)
  \/ FinishEat(p)
  \/ \E f \in ForksOf(p) : MakeRequest(p, f)
  \/ \E f \in ForksOf(p) : WithdrawRequest(p, f)
  \/ \E f \in Forks      : ServeRequest(p, f)

Next ==
  \E p \in P : NextP(p)

Spec ==
  Init /\ [][Next]_vars /\ \A p \in P : WF_vars(NextP(p))

(*
  Safety invariants
*)

TypeInv ==
  /\ status \in [P -> States]
  /\ owner \in [Forks -> P]
  /\ \A f \in Forks : owner[f] \in Endpoints(f)
  /\ clean \in [Forks -> BOOLEAN]
  /\ request \in [Forks -> ({"None"} \cup P)]
  /\ \A f \in Forks :
       request[f] = "None"
       \/ (request[f] \in Endpoints(f) /\ request[f] # owner[f])

MutualExclusion ==
  \A f \in Forks :
    ~ (status[Left(f)] = "Eating" /\ status[Right(f)] = "Eating")

Safety == TypeInv /\ MutualExclusion

(*
  Liveness properties
  - NonStarvation: each philosopher eats infinitely often.
  - HungryProgress: whenever a philosopher is hungry, it will eventually eat.
*)

NonStarvation ==
  \A p \in P : []<>(status[p] = "Eating")

HungryProgress ==
  \A p \in P : [](status[p] = "Hungry" => <> status[p] = "Eating")

=============================================================================