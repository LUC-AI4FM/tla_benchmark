---- MODULE BoundedQueueService ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Val, Procs, N, null

ASSUME N \in Nat /\ N > 0
ASSUME null \notin Val

VARIABLES queue, ret

vars == <<queue, ret>>

Results ==
    [kind : {"enq_ok", "full"}, val : Val]
    \cup [kind : {"deq_ok"}, val : Val]
    \cup [kind : {"empty"}, val : {null}]

IsKind(p, k) == ret[p] # null /\ ret[p].kind = k

TypeOK ==
    /\ queue \in Seq(Val)
    /\ ret \in [Procs -> {null} \cup Results]

Init ==
    /\ queue = << >>
    /\ ret = [p \in Procs |-> null]

LastElem(s) == s[Len(s)]
Front(s) == SubSeq(s, 1, Len(s) - 1)

EnqOk(p) ==
    /\ ret[p] = null
    /\ Len(queue) < N
    /\ \E v \in Val :
          /\ \/ queue' = Append(queue, v)
             \/ queue' = <<v>> \o queue
          /\ ret' = [ret EXCEPT ![p] = [kind |-> "enq_ok", val |-> v]]

EnqFull(p) ==
    /\ ret[p] = null
    /\ Len(queue) >= N
    /\ \E v \in Val :
          ret' = [ret EXCEPT ![p] = [kind |-> "full", val |-> v]]
    /\ UNCHANGED queue

DeqOk(p) ==
    /\ ret[p] = null
    /\ Len(queue) > 0
    /\ \/ /\ queue' = Tail(queue)
          /\ ret' = [ret EXCEPT ![p] = [kind |-> "deq_ok", val |-> Head(queue)]]
       \/ /\ queue' = Front(queue)
          /\ ret' = [ret EXCEPT ![p] = [kind |-> "deq_ok", val |-> LastElem(queue)]]

DeqEmpty(p) ==
    /\ ret[p] = null
    /\ Len(queue) = 0
    /\ ret' = [ret EXCEPT ![p] = [kind |-> "empty", val |-> null]]
    /\ UNCHANGED queue

Enq(p) == EnqOk(p) \/ EnqFull(p)
Deq(p) == DeqOk(p) \/ DeqEmpty(p)

Reset(p) ==
    /\ ret[p] # null
    /\ ret' = [ret EXCEPT ![p] = null]
    /\ UNCHANGED queue

Proc(p) == Enq(p) \/ Deq(p) \/ Reset(p)

Next == \E p \in Procs : Proc(p)

Fairness ==
    \A p \in Procs :
        /\ WF_vars(Proc(p))
        /\ SF_vars(EnqOk(p))
        /\ SF_vars(DeqOk(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* State constraint for model checking
Constraint == Len(queue) <= N

\* ---------------- Safety ----------------

CapacityInv == Len(queue) <= N

DeqSafe ==
    [][\A p \in Procs :
         (ret[p] = null /\ ret'[p] # null /\ ret'[p].kind = "deq_ok") =>
            /\ Len(queue) > 0
            /\ \/ /\ ret'[p].val = Head(queue)
                  /\ queue' = Tail(queue)
               \/ /\ ret'[p].val = LastElem(queue)
                  /\ queue' = Front(queue)
      ]_vars

EnqSafe ==
    [][\A p \in Procs :
         (ret[p] = null /\ ret'[p] # null /\ ret'[p].kind = "enq_ok") =>
            /\ Len(queue) < N
            /\ \/ queue' = Append(queue, ret'[p].val)
               \/ queue' = <<ret'[p].val>> \o queue
      ]_vars

FailureSafe ==
    [][\A p \in Procs :
         /\ (ret[p] = null /\ ret'[p] # null /\ ret'[p].kind = "full") =>
               (Len(queue) >= N /\ queue' = queue)
         /\ (ret[p] = null /\ ret'[p] # null /\ ret'[p].kind = "empty") =>
               (Len(queue) = 0 /\ queue' = queue)
      ]_vars

\* ---------------- Liveness ----------------

EnqProgress ==
    \A p \in Procs :
        ([]<>(ret[p] = null /\ Len(queue) < N)) => []<>(IsKind(p, "enq_ok"))

DeqProgress ==
    \A p \in Procs :
        ([]<>(ret[p] = null /\ Len(queue) > 0)) => []<>(IsKind(p, "deq_ok"))

ResetProgress ==
    \A p \in Procs : (ret[p] # null) ~> (ret[p] = null)

====