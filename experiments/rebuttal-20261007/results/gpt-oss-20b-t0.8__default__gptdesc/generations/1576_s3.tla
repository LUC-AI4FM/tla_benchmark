------------------------------ MODULE ConcurrentQueue ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Proc, Val, N

VARIABLES q, rV

(* Helper to extract the last element of a sequence *)
LastVal(s) == First(SubSeq(s, Len(s), 1))

TypeInvariant ==
  /\ q \in Seq(Val)
  /\ Len(q) <= N
  /\ rV \in [Proc -> {"okay", "full", "empty", "null"} ∪ Val]

Init ==
  /\ q = <<>>
  /\ rV = [p \in Proc |-> "null"]

EnqFront(p) ==
  /\ p \in Proc
  /\ LET v == CHOOSE x \in Val : TRUE IN
        (IF Len(q) < N THEN
            /\ q' = Cons(v, q)
            /\ rV' = [rV EXCEPT ![p] = "okay"]
         ELSE
            /\ q' = q
            /\ rV' = [rV EXCEPT ![p] = "full"])

EnqBack(p) ==
  /\ p \in Proc
  /\ LET v == CHOOSE x \in Val : TRUE IN
        (IF Len(q) < N THEN
            /\ q' = Append(q, v)
            /\ rV' = [rV EXCEPT ![p] = "okay"]
         ELSE
            /\ q' = q
            /\ rV' = [rV EXCEPT ![p] = "full"])

DeqHead(p) ==
  /\ p \in Proc
  /\ IF Len(q) > 0 THEN
        LET v == First(q) IN
            /\ q' = Rest(q)
            /\ rV' = [rV EXCEPT ![p] = v]
     ELSE
        /\ q' = q
        /\ rV' = [rV EXCEPT ![p] = "empty"]

DeqTail(p) ==
  /\ p \in Proc
  /\ IF Len(q) > 0 THEN
        LET v == LastVal(q) IN
            /\ q' = Init(q)
            /\ rV' = [rV EXCEPT ![p] = v]
     ELSE
        /\ q' = q
        /\ rV' = [rV EXCEPT ![p] = "empty"]

ProcAction(p) == EnqFront(p) \/ EnqBack(p) \/ DeqHead(p) \/ DeqTail(p)

Next == ∃ p \in Proc : ProcAction(p)

Spec ==
  Init
  /\ [][Next]_<<q, rV>>
  /\ TypeInvariant
  /\ WF_∀ p ∈ Proc : ProcAction(p)

=============================================================================