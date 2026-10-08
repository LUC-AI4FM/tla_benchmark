MODULE DiningPhilosophers
EXTENDS Naturals

CONSTANT N

(* Type and value constraints for the constant *)
N \in Nat          \* N is a natural number
N > 0              \* There must be at least one philosopher

VARIABLES pc, sem

\* State labels
Idle        == "Idle"
Right       == "Right"          \* right fork held (philosophers 1..N-1)
LeftFirst   == "LeftFirst"      \* left fork held by philosopher 0
Eating      == "Eating"

\* Initial state: all philosophers idle and all forks free
Init ==
  /\ pc = [i \in 0 .. N-1 |-> Idle]
  /\ sem = [j \in 0 .. N-1 |-> TRUE]

\* Individual actions for each philosopher

RightAcq(i) ==
  /\ i \in 1 .. N-1
  /\ pc[i] = Idle
  /\ sem[i] = TRUE
  /\ sem'   = [sem EXCEPT ![i] = FALSE]
  /\ pc'    = [pc EXCEPT ![i] = Right]

LeftAcq(i) ==
  /\ i \in 1 .. N-1
  /\ pc[i] = Right
  /\ sem[(i-1 + N) % N] = TRUE
  /\ sem'   = [sem EXCEPT ![(i-1 + N)%N] = FALSE]
  /\ pc'    = [pc EXCEPT ![i] = Eating]

LeftFirst(i) ==
  /\ i = 0
  /\ pc[i] = Idle
  /\ sem[N-1] = TRUE
  /\ sem'   = [sem EXCEPT ![N-1] = FALSE]
  /\ pc'    = [pc EXCEPT ![i] = LeftFirst]

RightAcq0(i) ==
  /\ i = 0
  /\ pc[i] = LeftFirst
  /\ sem[0] = TRUE
  /\ sem'   = [sem EXCEPT ![0] = FALSE]
  /\ pc'    = [pc EXCEPT ![i] = Eating]

DoneRest(i) ==
  /\ i \in 1 .. N-1
  /\ pc[i] = Eating
  /\ sem'   = [sem EXCEPT ![i] = TRUE, ![(i-1 + N)%N] = TRUE]
  /\ pc'    = [pc EXCEPT ![i] = Idle]

Done0 ==
  /\ i = 0
  /\ pc[i] = Eating
  /\ sem'   = [sem EXCEPT ![N-1] = TRUE, ![0] = TRUE]
  /\ pc'    = [pc EXCEPT ![i] = Idle]

\* Combined action for a philosopher
PhiloAction(i) ==
  RightAcq(i) \/ LeftAcq(i) \/ LeftFirst(i) \/ RightAcq0(i)
  \/ DoneRest(i) \/ Done0

Next == \E i \in 0 .. N-1 : PhiloAction(i)

\* Strong fairness for each philosopher
Fairness == \A i \in 0 .. N-1 : WF_vars(PhiloAction(i))

\* Safety invariant: no two adjacent philosophers eat simultaneously
SafeInv ==
  \A i \in 0 .. N-1 :
    LET j == (i+1) % N IN
      ~(pc[i] = Eating /\ pc[j] = Eating)

\* Liveness property: each philosopher eats infinitely often
StarveFree ==
  \A i \in 0 .. N-1 : []<>(pc[i] = Eating)

Spec == Init
       /\ [][Next]_(<<pc, sem>>)
       /\ Fairness
       /\ SafeInv
       /\ StarveFree

END MODULE