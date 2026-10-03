---- MODULE ByzantineOneStep ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  N,  \* The total number of processes
  F,  \* The maximum number of Byzantine faults
  T,  \* The threshold for decision
  V   \* The set of proposal values (e.g., {0, 1})

ASSUME
  /\ N \in 1..Nat
  /\ F \in 0..Nat
  /\ T \in 1..Nat
  /\ IsFiniteSet(V) /\ Cardinality(V) = 2
  /\ F < T
  /\ N >= 2 * T - 1

Procs == 1..N
Nil == CHOOSE v : v \notin V

VARIABLES
  faulty,    \* The set of faulty processes
  proposals, \* The initial value proposed by each process
  sent,      \* The value sent by each process
  state,     \* The state of each process
  decision   \* The decided value for each process

vars == <<faulty, proposals, sent, state, decision>>

TypeOK ==
  /\ faulty \subseteq Procs
  /\ Cardinality(faulty) <= F
  /\ proposals \in [Procs -> V]
  /\ sent \in [Procs -> V \union {Nil}]
  /\ state \in [Procs -> {"proposing", "receiving", "decided"}]
  /\ decision \in [Procs -> V \union {Nil}]

\* Initial state where all processes propose the same, first value in V.
InitAllV0 ==
  LET v0 == CHOOSE v \in V : TRUE IN
  /\ faulty = {}
  /\ proposals = [p \in Procs |-> v0]
  /\ sent = [p \in Procs |-> Nil]
  /\ state = [p \in Procs |-> "proposing"]
  /\ decision = [p \in Procs |-> Nil]

\* Initial state where all processes propose the same, second value in V.
InitAllV1 ==
  LET v0 == CHOOSE v \in V : TRUE IN
  LET v1 == CHOOSE v \in V \setminus {v0} : TRUE IN
  /\ faulty = {}
  /\ proposals = [p \in Procs |-> v1]
  /\ sent = [p \in Procs |-> Nil]
  /\ state = [p \in Procs |-> "proposing"]
  /\ decision = [p \in Procs |-> Nil]

Init == (InitAllV0 \/ InitAllV1)

\* A process p can become faulty at any time, as long as the total number of
\* faults does not exceed F.
BecomeFaulty ==
  /\ Cardinality(faulty) < F
  /\ \E p \in Procs \setminus faulty:
       /\ faulty' = faulty \cup {p}
       /\ UNCHANGED <<proposals, sent, state, decision>>

\* Process p sends its value. A correct process sends its proposal.
\* A faulty (Byzantine) process can send any value from V.
Propose(p) ==
  /\ state[p] = "proposing"
  /\ IF p \notin faulty
     THEN sent' = [sent EXCEPT ![p] = proposals[p]]
     ELSE \E v \in V : sent' = [sent EXCEPT ![p] = v]
  /\ state' = [state EXCEPT ![p] = "receiving"]
  /\ UNCHANGED <<faulty, proposals, decision>>

\* A correct process p decides on a value v if it has "received" at least T
\* messages for v. This action is enabled only after all processes have sent
\* their values (i.e., are no longer in the "proposing" state).
Decide(p) ==
  /\ p \notin faulty
  /\ state[p] = "receiving"
  /\ \A q \in Procs : state[q] # "proposing"
  /\ \E v \in V : Cardinality({q \in Procs : sent[q] = v}) >= T
  /\ LET v_to_decide == CHOOSE v \in V : Cardinality({q \in Procs : sent[q] = v}) >= T
     IN decision' = [decision EXCEPT ![p] = v_to_decide]
  /\ state' = [state EXCEPT ![p] = "decided"]
  /\ UNCHANGED <<faulty, proposals, sent>>

Next ==
  \/ BecomeFaulty
  \/ \E p \in Procs : Propose(p) \/ Decide(p)

\* Fairness condition: Weak fairness on the main step for each process. This
\* ensures that if a process can propose or decide, it will eventually do so.
Fairness == \A p \in Procs : WF_vars(Propose(p) \/ Decide(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* --- Properties ---

\* Safety: Agreement
\* All correct processes that decide, must decide on the same value.
Agreement ==
  \A p, q \in Procs \setminus faulty:
    (state[p] = "decided" /\ state[q] = "decided") => (decision[p] = decision[q])

\* Safety: Validity
\* If all correct processes initially propose the same value v, then any
\* correct process that decides must decide v.
Validity ==
  \A v \in V:
    LET CorrectProcs == Procs \setminus faulty IN
    (\A p \in CorrectProcs : proposals[p] = v) =>
      (\A q \in CorrectProcs : state[q] = "decided" => decision[q] = v)

\* Liveness: Termination
\* Every correct process eventually reaches the "decided" state.
Termination == \A p \in Procs \setminus faulty : <> (state[p] = "decided")

=============================================================================