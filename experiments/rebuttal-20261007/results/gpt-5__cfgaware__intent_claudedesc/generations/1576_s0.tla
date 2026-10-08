--------------------------- MODULE ConcurrentDeque ---------------------------
EXTENDS Sequences

CONSTANT Val

(*
  A simple concurrent double-ended queue (deque) with multiple processes.
  - Proc is a fixed set of process identifiers.
  - Val is a fixed set of values that can be enqueued (bound by the model).
  - N bounds the maximum queue length (state-space bound).
*)

Proc == {"p1", "p2", "p3"}
N == 3

(*
  Result values produced by operations.
  - "ok" for successful enqueues
  - dequeued value (in Val) for successful dequeues
  - "full" when reporting a full queue
  - "empty" when reporting an empty queue
  - "none" means no result is currently visible for the process
*)
OK == "ok"
FULL == "full"
EMPTY == "empty"
NoResult == "none"

VARIABLES q, res

vars == << q, res >>

Init ==
  /\ q = << >>
  /\ res = [p \in Proc |-> NoResult]

Last(s) == s[Len(s)]
ExceptLast(s) == IF Len(s) = 1 THEN << >> ELSE SubSeq(s, 1, Len(s) - 1)

EnqueueBack(p) ==
  \E v \in Val:
    /\ res[p] = NoResult
    /\ Len(q) < N
    /\ q' = Append(q, v)
    /\ res' = [res EXCEPT ![p] = OK]

EnqueueFront(p) ==
  \E v \in Val:
    /\ res[p] = NoResult
    /\ Len(q) < N
    /\ q' = << v >> \o q
    /\ res' = [res EXCEPT ![p] = OK]

DequeueFront(p) ==
  /\ res[p] = NoResult
  /\ Len(q) > 0
  /\ q' = Tail(q)
  /\ res' = [res EXCEPT ![p] = Head(q)]

DequeueBack(p) ==
  /\ res[p] = NoResult
  /\ Len(q) > 0
  /\ q' = ExceptLast(q)
  /\ res' = [res EXCEPT ![p] = Last(q)]

ReportFull(p) ==
  /\ res[p] = NoResult
  /\ Len(q) = N
  /\ q' = q
  /\ res' = [res EXCEPT ![p] = FULL]

ReportEmpty(p) ==
  /\ res[p] = NoResult
  /\ Len(q) = 0
  /\ q' = q
  /\ res' = [res EXCEPT ![p] = EMPTY]

ClearResult(p) ==
  /\ res[p] # NoResult
  /\ q' = q
  /\ res' = [res EXCEPT ![p] = NoResult]

DoOp(p) ==
  EnqueueBack(p) \/
  EnqueueFront(p) \/
  DequeueFront(p) \/
  DequeueBack(p) \/
  ReportFull(p) \/
  ReportEmpty(p)

Step(p) ==
  IF res[p] = NoResult
    THEN DoOp(p)
    ELSE ClearResult(p)

Next ==
  \E p \in Proc: Step(p)

(*
  State constraint for TLC (optional in config):
  ensure the queue never exceeds N elements.
*)
StateConstraint == Len(q) <= N

Spec ==
  Init /\ [][Next]_vars /\ \A p \in Proc: WF_vars(Step(p))
=============================================================================