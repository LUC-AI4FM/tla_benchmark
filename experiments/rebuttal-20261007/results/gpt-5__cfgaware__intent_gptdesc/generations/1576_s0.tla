--------------------------- MODULE BoundedQueue ---------------------------
EXTENDS Naturals, Sequences

(*
  Concurrent bounded queue service with per-client one-shot operations.
  Shared queue Q is a sequence over Val with maximum capacity N.
  Each client c ∈ Clients can perform:
    - Enqueue(v): if Len(Q) < N, insert v at head or tail (nondeterministically) and report EnqOK(v);
                  if Len(Q) = N, report EnqFull(v) without modifying Q.
    - Dequeue: if Len(Q) > 0, remove and return either head or tail (nondeterministically) and report DeqOK(v);
               if Len(Q) = 0, report DeqEmpty without modifying Q.
    - Reset: clear its return indicator back to Idle.
  All actions are atomic per client. Capacity is enforced in the transition relation.
*)

CONSTANTS
  Val,        \* Value domain for queue elements
  N,          \* Maximum capacity (a natural number)
  Clients,    \* Fixed, finite set of clients
  Null        \* Distinguished value not in Val, used as a neutral/absent marker

ASSUME
  /\ N \in Nat
  /\ Null \notin Val
  /\ Clients \subseteq STRING    \* no real restriction; documents that Clients is a set

(***************************************************************************)
(* State variables                                                          *)
(***************************************************************************)
VARIABLES
  Q,          \* queue as a sequence over Val
  ret         \* per-client return indicator (observable to the client)

Vars == << Q, ret >>

Kinds == {"Idle","EnqOK","EnqFull","DeqOK","DeqEmpty"}

ResultRec == [kind: Kinds, val: Val \cup {Null}]

RetIdle == [kind |-> "Idle", val |-> Null]

TypeOK ==
  /\ Q \in Seq(Val)
  /\ ret \in [Clients -> ResultRec]

(***************************************************************************)
(* Initialization                                                           *)
(***************************************************************************)
Init ==
  /\ Q = << >>
  /\ ret = [c \in Clients |-> RetIdle]

Idle(c) == ret[c].kind = "Idle"

(***************************************************************************)
(* Helper sequence operators                                                *)
(***************************************************************************)
First(s) == s[1]
LastEl(s) == s[Len(s)]
Rest(s) == SubSeq(s, 2, Len(s))
ButLast(s) == SubSeq(s, 1, Len(s)-1)

(***************************************************************************)
(* Per-client actions                                                       *)
(***************************************************************************)
EnqHead(c, v) ==
  /\ Idle(c)
  /\ v \in Val
  /\ Len(Q) < N
  /\ Q' = << v >> \o Q
  /\ ret' = [ret EXCEPT ![c] = [kind |-> "EnqOK", val |-> v]]

EnqTail(c, v) ==
  /\ Idle(c)
  /\ v \in Val
  /\ Len(Q) < N
  /\ Q' = Q \o << v >>
  /\ ret' = [ret EXCEPT ![c] = [kind |-> "EnqOK", val |-> v]]

EnqFull(c, v) ==
  /\ Idle(c)
  /\ v \in Val
  /\ Len(Q) = N
  /\ Q' = Q
  /\ ret' = [ret EXCEPT ![c] = [kind |-> "EnqFull", val |-> v]]

DeqFromHead(c) ==
  /\ Idle(c)
  /\ Len(Q) > 0
  /\ LET v == First(Q) IN
        /\ Q' = Rest(Q)
        /\ ret' = [ret EXCEPT ![c] = [kind |-> "DeqOK", val |-> v]]

DeqFromTail(c) ==
  /\ Idle(c)
  /\ Len(Q) > 0
  /\ LET v == LastEl(Q) IN
        /\ Q' = ButLast(Q)
        /\ ret' = [ret EXCEPT ![c] = [kind |-> "DeqOK", val |-> v]]

DeqEmpty(c) ==
  /\ Idle(c)
  /\ Len(Q) = 0
  /\ Q' = Q
  /\ ret' = [ret EXCEPT ![c] = [kind |-> "DeqEmpty", val |-> Null]]

Reset(c) ==
  /\ ~Idle(c)
  /\ Q' = Q
  /\ ret' = [ret EXCEPT ![c] = RetIdle]

Next_c(c) ==
  \/ \E v \in Val: EnqHead(c, v)
  \/ \E v \in Val: EnqTail(c, v)
  \/ \E v \in Val: EnqFull(c, v)
  \/ DeqFromHead(c)
  \/ DeqFromTail(c)
  \/ DeqEmpty(c)
  \/ Reset(c)

Next ==
  \E c \in Clients: Next_c(c)

(***************************************************************************)
(* Safety properties                                                        *)
(***************************************************************************)

\* Queue length never exceeds N (capacity bound)
CapacityInv == [](Len(Q) <= N)

\* Elements in Q are always from Val (type safety)
TypeSafety == [] (Q \in Seq(Val))

\* If a dequeue reports success in a step, it removed the head or tail element of the pre-state queue.
DeqOkRemoved ==
  [] ( \A c \in Clients:
         (ret[c].kind = "Idle" /\ ret'[c].kind = "DeqOK")
         =>
         /\ Len(Q) > 0
         /\ ( (Q' = Rest(Q) /\ ret'[c].val = First(Q))
             \/ (Q' = ButLast(Q) /\ ret'[c].val = LastEl(Q)) )
     )

\* If an enqueue reports success in a step, it actually placed that value at head or tail in the post-state queue.
EnqOkAdded ==
  [] ( \A c \in Clients:
         (ret[c].kind = "Idle" /\ ret'[c].kind = "EnqOK")
         =>
         ( Q' = << ret'[c].val >> \o Q \/ Q' = Q \o << ret'[c].val >> )
     )

Safety == CapacityInv /\ TypeSafety /\ DeqOkRemoved /\ EnqOkAdded

(***************************************************************************)
(* Liveness properties                                                      *)
(***************************************************************************)

\* Weak fairness: no client is permanently disabled from taking one of its actions.
Fairness == \A c \in Clients: WF_Vars(Next_c(c))
WF_Vars(A) == WF_VarsRec(Vars, A)
WF_VarsRec(vs, A) == WF_v(vs, A)
\* WF_v is the built-in WF_ operator; define a wrapper with the same semantics.
WF_v(vs, A) == WF_(vs)(A)

\* Progress under availability: any enqueue (resp. dequeue) attempt taken from a
\* state where capacity (resp. nonemptiness) holds must succeed in that very step.
AttemptSuccessWhenPossible ==
  /\ [] ( \A c \in Clients:
            (ret[c].kind = "Idle" /\ Len(Q) < N /\ ret'[c].kind \in {"EnqOK","EnqFull"})
            => ret'[c].kind = "EnqOK")
  /\ [] ( \A c \in Clients:
            (ret[c].kind = "Idle" /\ Len(Q) > 0 /\ ret'[c].kind \in {"DeqOK","DeqEmpty"})
            => ret'[c].kind = "DeqOK")

Liveness == Fairness /\ AttemptSuccessWhenPossible

(***************************************************************************)
(* Complete specification                                                   *)
(***************************************************************************)
Spec ==
  /\ Init
  /\ TypeOK
  /\ [][Next]_Vars
  /\ Fairness

=============================================================================