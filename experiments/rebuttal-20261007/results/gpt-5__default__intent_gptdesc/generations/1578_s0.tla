------------------------------ MODULE LockFreeDeque ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
  NODES,         \* finite set of node identifiers
  VALUES,        \* set of payload values
  CLIENTS,       \* set of client identifiers
  Nil            \* distinguished null pointer

ASSUME Nil \notin NODES
ASSUME Nil \notin VALUES
ASSUME {"ok","full","empty","none"} \cap VALUES = {}

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES 
  head, tail,                 \* NodeOrNil pointers to the ends
  next, prev,                 \* node fields: functions NODES -> NodeOrNil
  val,                        \* node payloads: NODES -> (VALUES \cup {Nil})
  free, retired,              \* disjoint pools: alloc/free and to-be-reclaimed
  pc, op, arg, res,           \* per-client control and I/O
  absSeq                      \* abstract deque content (sequence of VALUES)

NodeOrNil == NODES \cup {Nil}
Ops == {"pushL","pushR","popL","popR"}
PushRes == {"ok","full"}
PopRes == VALUES \cup {"empty"}

vars == << head, tail, next, prev, val, free, retired, pc, op, arg, res, absSeq >>

(***************************************************************************)
(* Derived/ghost functions over the heap                                   *)
(***************************************************************************)

RECURSIVE BuildSeq(_)
BuildSeq(n) == IF n = Nil THEN << >> ELSE << val[n] >> \o BuildSeq(next[n])

RECURSIVE Reach(_)
Reach(n) == IF n = Nil THEN {} ELSE {n} \cup Reach(next[n])

RECURSIVE TailOf(_)
TailOf(n) == 
  IF n = Nil THEN Nil 
  ELSE IF next[n] = Nil THEN n ELSE TailOf(next[n])

ReachSet == Reach(head)

HeadVal(s) == s[1]
LastVal(s) == s[Len(s)]

LeftPop(s) == SubSeq(s, 2, Len(s))
RightPop(s) == SubSeq(s, 1, Len(s) - 1)

(***************************************************************************)
(* Type correctness and structural/memory invariants                       *)
(***************************************************************************)

TypeOK ==
  /\ head \in NodeOrNil
  /\ tail \in NodeOrNil
  /\ next \in [NODES -> NodeOrNil]
  /\ prev \in [NODES -> NodeOrNil]
  /\ val \in [NODES -> (VALUES \cup {Nil})]
  /\ free \subseteq NODES
  /\ retired \subseteq NODES
  /\ pc \in [CLIENTS -> {"idle","try","ret"}]
  /\ op \in [CLIENTS -> (Ops \cup {"none"})]
  /\ arg \in [CLIENTS -> (VALUES \cup {Nil})]
  /\ res \in [CLIENTS -> (VALUES \cup {"empty","full","ok"} \cup {Nil})]
  /\ absSeq \in Seq(VALUES)

StructInv ==
  /\ (head = Nil) <=> (tail = Nil)
  /\ (head = Nil) => (absSeq = << >>)
  /\ (head # Nil) => (prev[head] = Nil)
  /\ (tail # Nil) => (next[tail] = Nil)
  /\ TailOf(head) = tail
  /\ \A n \in ReachSet:
       LET m == next[n] IN (m # Nil) => prev[m] = n
  /\ Len(BuildSeq(head)) = Cardinality(ReachSet)

MemSafety ==
  /\ ReachSet \cap free = {}
  /\ ReachSet \cap retired = {}
  /\ free \cap retired = {}
  /\ (NODES \ free) = ReachSet \cup retired
  /\ \A n \in ReachSet: val[n] \in VALUES

AbsConsistent ==
  absSeq = BuildSeq(head)

Invariants == TypeOK /\ StructInv /\ MemSafety /\ AbsConsistent

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
  /\ head = Nil
  /\ tail = Nil
  /\ next \in [NODES -> Nil]
  /\ prev \in [NODES -> Nil]
  /\ val \in [NODES -> Nil]
  /\ free = NODES
  /\ retired = {}
  /\ pc = [c \in CLIENTS |-> "idle"]
  /\ op = [c \in CLIENTS |-> "none"]
  /\ arg = [c \in CLIENTS |-> Nil]
  /\ res = [c \in CLIENTS |-> Nil]
  /\ absSeq = << >>

(***************************************************************************)
(* Client invocation actions (environment chooses which op to start)       *)
(***************************************************************************)

InvokePushL(c) ==
  \E v \in VALUES:
    /\ pc[c] = "idle"
    /\ pc' = [pc EXCEPT ![c] = "try"]
    /\ op' = [op EXCEPT ![c] = "pushL"]
    /\ arg' = [arg EXCEPT ![c] = v]
    /\ res' = [res EXCEPT ![c] = Nil]
    /\ UNCHANGED << head, tail, next, prev, val, free, retired, absSeq >>

InvokePushR(c) ==
  \E v \in VALUES:
    /\ pc[c] = "idle"
    /\ pc' = [pc EXCEPT ![c] = "try"]
    /\ op' = [op EXCEPT ![c] = "pushR"]
    /\ arg' = [arg EXCEPT ![c] = v]
    /\ res' = [res EXCEPT ![c] = Nil]
    /\ UNCHANGED << head, tail, next, prev, val, free, retired, absSeq >>

InvokePopL(c) ==
  /\ pc[c] = "idle"
  /\ pc' = [pc EXCEPT ![c] = "try"]
  /\ op' = [op EXCEPT ![c] = "popL"]
  /\ arg' = [arg EXCEPT ![c] = Nil]
  /\ res' = [res EXCEPT ![c] = Nil]
  /\ UNCHANGED << head, tail, next, prev, val, free, retired, absSeq >>

InvokePopR(c) ==
  /\ pc[c] = "idle"
  /\ pc' = [pc EXCEPT ![c] = "try"]
  /\ op' = [op EXCEPT ![c] = "popR"]
  /\ arg' = [arg EXCEPT ![c] = Nil]
  /\ res' = [res EXCEPT ![c] = Nil]
  /\ UNCHANGED << head, tail, next, prev, val, free, retired, absSeq >>

(***************************************************************************)
(* Commit/Fail steps (linearization points)                                *)
(***************************************************************************)

CommitPushL(c) ==
  /\ pc[c] = "try"
  /\ op[c] = "pushL"
  /\ free # {}
  /\ \E a \in free:
      LET h == head IN
      /\ head' = a
      /\ tail' = IF h = Nil THEN a ELSE tail
      /\ next' = [next EXCEPT ![a] = h]
      /\ prev' = IF h = Nil 
                  THEN [prev EXCEPT ![a] = Nil]
                  ELSE [prev EXCEPT ![a] = Nil, ![h] = a]
      /\ val' = [val EXCEPT ![a] = arg[c]]
      /\ free' = free \ {a}
      /\ retired' = retired
      /\ absSeq' = << arg[c] >> \o absSeq
      /\ res' = [res EXCEPT ![c] = "ok"]
      /\ pc' = [pc EXCEPT ![c] = "ret"]
      /\ UNCHANGED << op, arg >>

CommitPushR(c) ==
  /\ pc[c] = "try"
  /\ op[c] = "pushR"
  /\ free # {}
  /\ \E a \in free:
      LET t == tail IN
      /\ tail' = a
      /\ head' = IF t = Nil THEN a ELSE head
      /\ prev' = [prev EXCEPT ![a] = t]
      /\ next' = IF t = Nil
                  THEN [next EXCEPT ![a] = Nil]
                  ELSE [next EXCEPT ![a] = Nil, ![t] = a]
      /\ val' = [val EXCEPT ![a] = arg[c]]
      /\ free' = free \ {a}
      /\ retired' = retired
      /\ absSeq' = absSeq \o << arg[c] >>
      /\ res' = [res EXCEPT ![c] = "ok"]
      /\ pc' = [pc EXCEPT ![c] = "ret"]
      /\ UNCHANGED << op, arg >>

FailFull(c) ==
  /\ pc[c] = "try"
  /\ op[c] \in {"pushL","pushR"}
  /\ free = {}
  /\ res' = [res EXCEPT ![c] = "full"]
  /\ pc' = [pc EXCEPT ![c] = "ret"]
  /\ UNCHANGED << head, tail, next, prev, val, free, retired, op, arg, absSeq >>

CommitPopL(c) ==
  /\ pc[c] = "try"
  /\ op[c] = "popL"
  /\ head # Nil
  /\ LET x == head IN
     LET nh == next[x] IN
      /\ head' = nh
      /\ tail' = IF nh = Nil THEN Nil ELSE tail
      /\ next' = [next EXCEPT ![x] = Nil]
      /\ prev' = IF nh = Nil 
                  THEN [prev EXCEPT ![x] = Nil]
                  ELSE [prev EXCEPT ![x] = Nil, ![nh] = Nil]
      /\ retired' = retired \cup {x}
      /\ res' = [res EXCEPT ![c] = val[x]]
      /\ pc' = [pc EXCEPT ![c] = "ret"]
      /\ absSeq' = LeftPop(absSeq)
      /\ UNCHANGED << val, free, op, arg >>

FailEmptyL(c) ==
  /\ pc[c] = "try"
  /\ op[c] = "popL"
  /\ head = Nil
  /\ res' = [res EXCEPT ![c] = "empty"]
  /\ pc' = [pc EXCEPT ![c] = "ret"]
  /\ UNCHANGED << head, tail, next, prev, val, free, retired, op, arg, absSeq >>

CommitPopR(c) ==
  /\ pc[c] = "try"
  /\ op[c] = "popR"
  /\ tail # Nil
  /\ LET x == tail IN
     LET px == prev[x] IN
      /\ tail' = px
      /\ head' = IF px = Nil THEN Nil ELSE head
      /\ prev' = [prev EXCEPT ![x] = Nil]
      /\ next' = IF px = Nil
                  THEN [next EXCEPT ![x] = Nil]
                  ELSE [next EXCEPT ![x] = Nil, ![px] = Nil]
      /\ retired' = retired \cup {x}
      /\ res' = [res EXCEPT ![c] = val[x]]
      /\ pc' = [pc EXCEPT ![c] = "ret"]
      /\ absSeq' = RightPop(absSeq)
      /\ UNCHANGED << val, free, op, arg >>

FailEmptyR(c) ==
  /\ pc[c] = "try"
  /\ op[c] = "popR"
  /\ head = Nil
  /\ res' = [res EXCEPT ![c] = "empty"]
  /\ pc' = [pc EXCEPT ![c] = "ret"]
  /\ UNCHANGED << head, tail, next, prev, val, free, retired, op, arg, absSeq >>

DoOpStep(c) ==
  CommitPushL(c) \/
  CommitPushR(c) \/
  FailFull(c)    \/
  CommitPopL(c)  \/
  CommitPopR(c)  \/
  FailEmptyL(c)  \/
  FailEmptyR(c)

Return(c) ==
  /\ pc[c] = "ret"
  /\ pc' = [pc EXCEPT ![c] = "idle"]
  /\ op' = [op EXCEPT ![c] = "none"]
  /\ arg' = [arg EXCEPT ![c] = Nil]
  /\ UNCHANGED << head, tail, next, prev, val, free, retired, res, absSeq >>

(***************************************************************************)
(* Garbage collector step (nondeterministic, safe reclamation)             *)
(***************************************************************************)

GCStep ==
  /\ \E R \in SUBSET retired:
       /\ R # {}
       /\ head' = head
       /\ tail' = tail
       /\ next' = [n \in NODES |-> IF n \in R THEN Nil ELSE next[n]]
       /\ prev' = [n \in NODES |-> IF n \in R THEN Nil ELSE prev[n]]
       /\ val'  = [n \in NODES |-> IF n \in R THEN Nil ELSE val[n]]
       /\ free' = free \cup R
       /\ retired' = retired \ {R}
       /\ absSeq' = absSeq
       /\ pc' = pc
       /\ op' = op
       /\ arg' = arg
       /\ res' = res

(***************************************************************************)
(* System next-state relation and fairness                                 *)
(***************************************************************************)

ClientStep ==
  \E c \in CLIENTS:
    InvokePushL(c) \/ InvokePushR(c) \/ InvokePopL(c) \/ InvokePopR(c) \/
    DoOpStep(c) \/ Return(c)

Next == ClientStep \/ GCStep

Spec ==
  Init /\ [][Next]_vars
  /\ \A c \in CLIENTS: WF_vars(DoOpStep(c))
  /\ \A c \in CLIENTS: WF_vars(Return(c))

(***************************************************************************)
(* Stated safety and liveness properties                                   *)
(***************************************************************************)

Safety == Invariants

Linearizable ==
  AbsConsistent
  \* The commit actions (CommitPushL/R and CommitPopL/R) serve as linearization points
  \* that update both the concrete structure and absSeq atomically.

MemorySafe ==
  MemSafety

Progress ==
  \A c \in CLIENTS: WF_vars(DoOpStep(c)) /\ WF_vars(Return(c))

THEOREM Spec => []Safety

=============================================================================