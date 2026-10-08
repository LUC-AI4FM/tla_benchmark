----------------------------- MODULE BoundedQueue -----------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    C,          \* set of clients
    Val,        \* value domain
    N,          \* maximum capacity
    NULL        \* neutral value not in Val

ASSUME N \in Nat
ASSUME NULL \notin Val

(****************************************************************
 State variables
****************************************************************)
VARIABLES 
    q,          \* the queue as a sequence of values in Val
    ret,        \* per-client return indicator: record [kind, val]
    op,         \* per-client chosen operation: "enq" or "deq"
    enqCnt,     \* ghost: counts of successful enqueues per value
    deqCnt      \* ghost: counts of successful dequeues per value

vars == << q, ret, op, enqCnt, deqCnt >>

(****************************************************************
 Helper definitions
****************************************************************)
Kinds == {"neutral", "enqOk", "enqFull", "deqOk", "deqEmpty"}

Prepend(s, v) == <<v>> \o s

Last(s) == s[Len(s)]

ButLast(s) == IF Len(s) = 0 THEN <<>> ELSE IF Len(s) = 1 THEN <<>> ELSE SubSeq(s, 1, Len(s) - 1)

Occurs(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })

NotFull == Len(q) < N
NonEmpty == Len(q) > 0

EnqSuccessState(c) == ret[c].kind = "enqOk"
DeqSuccessState(c) == ret[c].kind = "deqOk"

EnqReady(c) == ret[c].kind = "neutral" /\ op[c] = "enq" /\ NotFull
DeqReady(c) == ret[c].kind = "neutral" /\ op[c] = "deq" /\ NonEmpty

(****************************************************************
 Initial predicate
****************************************************************)
Init ==
    /\ q = <<>>
    /\ ret = [c \in C |-> [kind |-> "neutral", val |-> NULL]]
    /\ op \in [C -> {"enq", "deq"}]
    /\ enqCnt = [v \in Val |-> 0]
    /\ deqCnt = [v \in Val |-> 0]

(****************************************************************
 Per-client actions
****************************************************************)
ChooseOp(c) ==
    /\ c \in C
    /\ ret[c].kind = "neutral"
    /\ \E o \in {"enq","deq"}:
         /\ op' = [op EXCEPT ![c] = o]
         /\ UNCHANGED << q, ret, enqCnt, deqCnt >>

EnqAttempt(c) ==
    /\ c \in C
    /\ ret[c].kind = "neutral"
    /\ op[c] = "enq"
    /\ (
         /\ Len(q) < N
         /\ \E v \in Val:
              /\ (q' = Append(q, v) \/ q' = Prepend(q, v))
              /\ ret' = [ret EXCEPT ![c] = [kind |-> "enqOk", val |-> v]]
              /\ enqCnt' = [enqCnt EXCEPT ![v] = @ + 1]
              /\ UNCHANGED << op, deqCnt >>
       \/
         /\ Len(q) = N
         /\ q' = q
         /\ ret' = [ret EXCEPT ![c] = [kind |-> "enqFull", val |-> NULL]]
         /\ UNCHANGED << op, enqCnt, deqCnt >>
       )

DeqAttempt(c) ==
    /\ c \in C
    /\ ret[c].kind = "neutral"
    /\ op[c] = "deq"
    /\ (
         /\ Len(q) > 0
         /\ (
               \* remove head
               ( LET x == q[1] IN
                   /\ q' = IF Len(q) = 1 THEN <<>> ELSE SubSeq(q, 2, Len(q))
                   /\ ret' = [ret EXCEPT ![c] = [kind |-> "deqOk", val |-> x]]
                   /\ deqCnt' = [deqCnt EXCEPT ![x] = @ + 1]
               )
             \/
               \* remove tail
               ( LET x == Last(q) IN
                   /\ q' = ButLast(q)
                   /\ ret' = [ret EXCEPT ![c] = [kind |-> "deqOk", val |-> x]]
                   /\ deqCnt' = [deqCnt EXCEPT ![x] = @ + 1]
               )
           )
         /\ UNCHANGED << op, enqCnt >>
       \/
         /\ Len(q) = 0
         /\ q' = q
         /\ ret' = [ret EXCEPT ![c] = [kind |-> "deqEmpty", val |-> NULL]]
         /\ UNCHANGED << op, enqCnt, deqCnt >>
       )

Reset(c) ==
    /\ c \in C
    /\ ret[c].kind # "neutral"
    /\ ret' = [ret EXCEPT ![c] = [kind |-> "neutral", val |-> NULL]]
    /\ UNCHANGED << q, op, enqCnt, deqCnt >>

Step(c) == ChooseOp(c) \/ EnqAttempt(c) \/ DeqAttempt(c) \/ Reset(c)

AttemptOrReset(c) == EnqAttempt(c) \/ DeqAttempt(c) \/ Reset(c)

(****************************************************************
 Next-state relation
****************************************************************)
Next == \E c \in C: Step(c)

(****************************************************************
 Safety invariants
****************************************************************)
TypeInv ==
    /\ q \in Seq(Val)
    /\ Len(q) <= N
    /\ ret \in [C -> [kind: Kinds, val: Val \cup {NULL}]]
    /\ \A c \in C:
         /\ (ret[c].kind \in {"enqOk","deqOk"} => ret[c].val \in Val)
         /\ (ret[c].kind \in {"neutral","enqFull","deqEmpty"} => ret[c].val = NULL)
    /\ op \in [C -> {"enq","deq"}]
    /\ enqCnt \in [Val -> Nat]
    /\ deqCnt \in [Val -> Nat]
    /\ \A v \in Val: Occurs(q, v) = enqCnt[v] - deqCnt[v]

CapacityInvariant == Len(q) <= N

NoSpuriousNoDupInvariant == \A v \in Val: deqCnt[v] <= enqCnt[v]

SafetyInvariants == TypeInv /\ CapacityInvariant /\ NoSpuriousNoDupInvariant

(****************************************************************
 Liveness: fairness and progress properties
****************************************************************)
Fairness == \A c \in C: WF_vars(AttemptOrReset(c))

EnqProgress(c) == ([]<>(EnqReady(c))) => ([]<>(EnqSuccessState(c)))
DeqProgress(c) == ([]<>(DeqReady(c))) => ([]<>(DeqSuccessState(c)))

LivenessProps == \A c \in C: EnqProgress(c) /\ DeqProgress(c)

(****************************************************************
 Full specification
****************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================