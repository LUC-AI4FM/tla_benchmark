---------------------------- MODULE Squares ----------------------------
(***************************************************************************)
(* A sequential algorithm that fills an array a[0..n] with square numbers. *)
(* Entry 0 already equals 0^2 after initialization, so the loop performs   *)
(* exactly n iterations.  Iteration j (j = 1..n) computes x = j^2 and      *)
(* writes it to a[j].                                                      *)
(*                                                                         *)
(*   i  : the iteration counter.  It is also the highest index known to    *)
(*        be correct.  It starts at 0, only increases, and never exceeds n.*)
(*   x  : a temporary register that holds the value about to be written.   *)
(*   pc : the control state, which is "loop", "write" or "Done".           *)
(*                                                                         *)
(* n is chosen nondeterministically from the constant set NSet at          *)
(* initialization.  It never changes after that.                           *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT NSet

ASSUME NSet \subseteq Nat

VARIABLES n, a, i, x, pc

vars == <<n, a, i, x, pc>>

-----------------------------------------------------------------------------
Init ==
    /\ n \in NSet
    /\ a = [k \in 0..n |-> 0]
    /\ i = 0
    /\ x = 0
    /\ pc = "loop"

(* Loop test: if more entries remain, compute the next square into x. *)
Loop ==
    /\ pc = "loop"
    /\ IF i < n
          THEN /\ x' = (i + 1) * (i + 1)
               /\ pc' = "write"
          ELSE /\ pc' = "Done"
               /\ x' = x
    /\ UNCHANGED <<n, a, i>>

(* Write step: update exactly one entry, a[i+1], and advance the counter. *)
Write ==
    /\ pc = "write"
    /\ i + 1 \in 0..n
    /\ a' = [a EXCEPT ![i + 1] = x]
    /\ i' = i + 1
    /\ pc' = "loop"
    /\ UNCHANGED <<n, x>>

(* Allow stuttering after termination so that the model has no deadlock. *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Loop \/ Write \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop \/ Write)

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ n \in NSet
    /\ a \in [0..n -> Nat]
    /\ i \in 0..n
    /\ x \in Nat
    /\ pc \in {"loop", "write", "Done"}

(* Bounds safety: any index that is about to be written lies in 0..n. *)
BoundsSafe ==
    /\ i \in 0..n
    /\ (pc = "write") => (i + 1 \in 0..n)

(* Correct update invariant: entries 0..i hold the squares 0^2..i^2. *)
(* Entries above i are still zero.                                    *)
CorrectPrefix ==
    /\ \A k \in 0..i : a[k] = k * k
    /\ \A k \in (i + 1)..n : a[k] = 0

(* While in the write state, x holds the value for the next entry. *)
XCorrect == (pc = "write") => (x = (i + 1) * (i + 1))

(* At most n iterations are performed. *)
IterationBound == i <= n

(* Postcondition once the algorithm has finished. *)
PostCondition == \A k \in 0..n : a[k] = k * k

DoneCorrect == (pc = "Done") => (i = n /\ PostCondition)

Inv ==
    /\ TypeOK
    /\ BoundsSafe
    /\ CorrectPrefix
    /\ XCorrect
    /\ IterationBound
    /\ DoneCorrect

(* Single writer: each step changes at most one entry of a, and that  *)
(* entry is the in-bounds index i+1, written during a Write step.     *)
SingleWriter ==
    [][ \A k \in 0..n :
          (a'[k] # a[k]) => (k = i + 1 /\ k \in 0..n /\ pc = "write") ]_vars

(* The iteration counter increases monotonically by at most one. *)
Monotone == [][ i' = i \/ i' = i + 1 ]_vars

(* The parameter n and the domain of a never change. *)
NFixed == [][ n' = n /\ DOMAIN a' = DOMAIN a ]_vars

-----------------------------------------------------------------------------
(* Liveness property *)

Termination == <>(pc = "Done" /\ PostCondition)

=============================================================================