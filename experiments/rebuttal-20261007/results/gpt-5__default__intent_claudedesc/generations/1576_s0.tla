--------------------------- MODULE ConcurrentDeque ---------------------------

EXTENDS Naturals, Sequences

CONSTANTS Proc, Values, N

VARIABLES q, res

(*
  Result is either:
    - a record with only a 'type' field in {"none","success","full","empty"}, or
    - a record with 'type' = "value" and a 'val' in Values.
*)
Result ==
  [type: {"none","success","full","empty"}] \cup [type: {"value"}, val: Values]

IsEmpty == q = <<>>
IsFull  == Len(q) = N

Init ==
  /\ q = <<>>
  /\ res = [p \in Proc |-> [type |-> "none"]]

EnqBack(p) ==
  \E v \in Values:
    /\ ~IsFull
    /\ q' = Append(q, v)
    /\ res' = [res EXCEPT ![p] = [type |-> "success"]]

EnqFront(p) ==
  \E v \in Values:
    /\ ~IsFull
    /\ q' = <<v>> \o q
    /\ res' = [res EXCEPT ![p] = [type |-> "success"]]

DeqFront(p) ==
  /\ ~IsEmpty
  /\ LET v == Head(q) IN
       /\ q' = Tail(q)
       /\ res' = [res EXCEPT ![p] = [type |-> "value", val |-> v]]

DeqBack(p) ==
  /\ ~IsEmpty
  /\ LET v == q[Len(q)] IN
       /\ q' = SubSeq(q, 1, Len(q) - 1)
       /\ res' = [res EXCEPT ![p] = [type |-> "value", val |-> v]]

ReportFull(p) ==
  /\ IsFull
  /\ UNCHANGED q
  /\ res' = [res EXCEPT ![p] = [type |-> "full"]]

ReportEmpty(p) ==
  /\ IsEmpty
  /\ UNCHANGED q
  /\ res' = [res EXCEPT ![p] = [type |-> "empty"]]

Clear(p) ==
  /\ res[p].type # "none"
  /\ UNCHANGED q
  /\ res' = [res EXCEPT ![p] = [type |-> "none"]]

ProcStep(p) ==
  EnqBack(p) \/ EnqFront(p) \/
  DeqFront(p) \/ DeqBack(p) \/
  ReportFull(p) \/ ReportEmpty(p) \/
  Clear(p)

Next ==
  \E p \in Proc: ProcStep(p)

vars == << q, res >>

Spec ==
  Init /\ [][Next]_vars /\ \A p \in Proc: WF_vars(ProcStep(p))

(*
  State constraint and simple type invariant for use with model checking.
*)
QueueBound == Len(q) <= N
StateConstraint == QueueBound

TypeInv ==
  /\ q \in Seq(Values)
  /\ res \in [Proc -> Result]

=============================================================================