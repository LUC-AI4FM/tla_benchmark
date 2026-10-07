------------------------------- MODULE ConcurrentQueue -------------------------------

EXTENDS Naturals, Sequences

CONSTANTS Procs, Val, N

ASSUME N \in Nat
ASSUME {"okay", "full", "empty", "null"} \cap Val = {}

VARIABLES q, pc, rV

Vars == << q, pc, rV >>

Init ==
  /\ q = << >>
  /\ pc = [self \in Procs |-> "run"]
  /\ rV = [self \in Procs |-> "null"]

EnqFront(self) ==
  \E x \in Val:
    /\ pc[self] = "run"
    /\ IF Len(q) < N
         THEN /\ q' = <<x>> \o q
              /\ rV' = [rV EXCEPT ![self] = "okay"]
         ELSE /\ q' = q
              /\ rV' = [rV EXCEPT ![self] = "full"]
    /\ UNCHANGED pc

EnqBack(self) ==
  \E x \in Val:
    /\ pc[self] = "run"
    /\ IF Len(q) < N
         THEN /\ q' = q \o <<x>>
              /\ rV' = [rV EXCEPT ![self] = "okay"]
         ELSE /\ q' = q
              /\ rV' = [rV EXCEPT ![self] = "full"]
    /\ UNCHANGED pc

DeqFront(self) ==
  /\ pc[self] = "run"
  /\ IF Len(q) > 0
       THEN /\ rV' = [rV EXCEPT ![self] = Head(q)]
            /\ q' = Tail(q)
       ELSE /\ rV' = [rV EXCEPT ![self] = "empty"]
            /\ q' = q
  /\ UNCHANGED pc

DeqBack(self) ==
  /\ pc[self] = "run"
  /\ IF Len(q) > 0
       THEN LET last == q[Len(q)]
                rest == SubSeq(q, 1, Len(q) - 1)
            IN  /\ rV' = [rV EXCEPT ![self] = last]
                /\ q' = rest
       ELSE /\ rV' = [rV EXCEPT ![self] = "empty"]
            /\ q' = q
  /\ UNCHANGED pc

P(self) ==
  EnqFront(self) \/ EnqBack(self) \/ DeqFront(self) \/ DeqBack(self)

Next ==
  \E self \in Procs: P(self)

TypeOK ==
  /\ q \in Seq(Val)
  /\ pc \in [Procs -> {"run"}]
  /\ rV \in [Procs -> (Val \cup {"okay", "full", "empty", "null"})]

QueueBound ==
  Len(q) <= N

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A self \in Procs: WF_Vars(P(self))
  /\ []QueueBound

=============================================================================