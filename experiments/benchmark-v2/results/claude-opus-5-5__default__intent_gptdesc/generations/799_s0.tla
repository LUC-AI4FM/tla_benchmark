---------------------------- MODULE DistributedSeqMax ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    MaxLen,     \* maximum length of any input sequence
    MaxVal,     \* maximum value of any sequence element
    Procs       \* set of concurrent worker processes

ASSUME MaxLen \in Nat
ASSUME MaxVal \in Nat
ASSUME Procs # {}

-----------------------------------------------------------------------------
(* All finite sequences respecting the length and element bounds.          *)
BSeq == UNION { [1..n -> 0..MaxVal] : n \in 0..MaxLen }

(* An index is a pair <<s, i>>: sequence s and position i within it.        *)
Positions(S) == { <<s, i>> : s \in S, i \in 1..Len(s) }

AllIndices == { <<s, i>> : s \in BSeq, i \in 1..MaxLen }

Elem(x) == x[1][x[2]]

NoBest  == [found |-> FALSE, idx |-> <<<<>>, 0>>, val |-> 0]
Pending == [status |-> "pending", idx |-> <<<<>>, 0>>, val |-> 0]

-----------------------------------------------------------------------------
VARIABLES
    input,   \* the (nondeterministic) set of bounded input sequences
    phase,   \* "init" | "running" | "done"
    todo,    \* indices not yet claimed by any worker
    local,   \* local[p]: set holding the index worker p is examining ({} = idle)
    best,    \* best element found so far
    result   \* reported result

vars == <<input, phase, todo, local, best, result>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ input \subseteq BSeq
    /\ IsFiniteSet(input)
    /\ phase \in {"init", "running", "done"}
    /\ todo \subseteq Positions(input)
    /\ local \in [Procs -> SUBSET Positions(input)]
    /\ \A p \in Procs : Cardinality(local[p]) <= 1
    /\ best.found \in BOOLEAN
    /\ best.val \in 0..MaxVal
    /\ result.status \in {"pending", "max", "nomax"}
    /\ result.val \in 0..MaxVal

-----------------------------------------------------------------------------
Init ==
    /\ input \in SUBSET BSeq
    /\ phase = "init"
    /\ todo = {}
    /\ local = [p \in Procs |-> {}]
    /\ best = NoBest
    /\ result = Pending

(* Nondeterministically introduce another bounded sequence before start.   *)
AddSeq ==
    /\ phase = "init"
    /\ \E s \in BSeq : input' = input \cup {s}
    /\ UNCHANGED <<phase, todo, local, best, result>>

Start ==
    /\ phase = "init"
    /\ phase' = "running"
    /\ todo' = Positions(input)
    /\ UNCHANGED <<input, local, best, result>>

(* Worker p claims an unexamined index.                                    *)
Take(p) ==
    /\ phase = "running"
    /\ local[p] = {}
    /\ \E x \in todo :
         /\ todo' = todo \ {x}
         /\ local' = [local EXCEPT ![p] = {x}]
    /\ UNCHANGED <<input, phase, best, result>>

(* Worker p compares its element with the current best (atomic update).   *)
Compare(p) ==
    /\ phase = "running"
    /\ \E x \in local[p] :
         /\ best' = IF ~best.found \/ Elem(x) > best.val
                       THEN [found |-> TRUE, idx |-> x, val |-> Elem(x)]
                       ELSE best
         /\ local' = [local EXCEPT ![p] = {}]
    /\ UNCHANGED <<input, phase, todo, result>>

Finish ==
    /\ phase = "running"
    /\ todo = {}
    /\ \A p \in Procs : local[p] = {}
    /\ phase' = "done"
    /\ result' = IF best.found
                    THEN [status |-> "max", idx |-> best.idx, val |-> best.val]
                    ELSE [status |-> "nomax", idx |-> <<<<>>, 0>>, val |-> 0]
    /\ UNCHANGED <<input, todo, local, best>>

Terminated ==
    /\ phase = "done"
    /\ UNCHANGED vars

Next ==
    \/ AddSeq
    \/ Start
    \/ \E p \in Procs : Take(p) \/ Compare(p)
    \/ Finish
    \/ Terminated

Fairness ==
    /\ WF_vars(Start)
    /\ \A p \in Procs : WF_vars(Take(p)) /\ WF_vars(Compare(p))
    /\ WF_vars(Finish)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

Examined == Positions(input) \ (todo \cup UNION { local[p] : p \in Procs })

(* Partial correctness of the running best. *)
BestInv ==
    phase = "running" =>
      /\ best.found =>
           /\ best.idx \in Positions(input)
           /\ best.val = Elem(best.idx)
           /\ \A q \in Examined : Elem(q) <= best.val
      /\ (~best.found) => Examined = {}

(* Final correctness: reported value is an element and is maximal. *)
Correctness ==
    phase = "done" =>
      /\ result.status \in {"max", "nomax"}
      /\ result.status = "max" =>
           /\ result.idx \in Positions(input)
           /\ result.val = Elem(result.idx)
           /\ \A q \in Positions(input) : Elem(q) <= result.val
      /\ (result.status = "nomax") <=> (Positions(input) = {})

ResultOnlyWhenDone ==
    (result.status # "pending") <=> (phase = "done")

(* All accessed indices and values remain within bounds. *)
BoundsInv ==
    /\ \A s \in input : Len(s) <= MaxLen /\ \A i \in 1..Len(s) : s[i] \in 0..MaxVal
    /\ \A x \in todo \cup UNION { local[p] : p \in Procs } :
         /\ x \in AllIndices
         /\ x[2] \in 1..Len(x[1])
         /\ Elem(x) \in 0..MaxVal
    /\ best.found => (best.idx[2] \in 1..MaxLen /\ best.val \in 0..MaxVal)
    /\ result.status = "max" => (result.idx[2] \in 1..MaxLen /\ result.val \in 0..MaxVal)

Safety == TypeOK /\ BestInv /\ Correctness /\ ResultOnlyWhenDone /\ BoundsInv

-----------------------------------------------------------------------------
(* Liveness properties *)

Termination == <>(phase = "done")

EventuallyReports == <>[](result.status \in {"max", "nomax"})

LeadsToResult == (phase \in {"init", "running"}) ~> (result.status # "pending")

THEOREM Spec => []Safety
THEOREM Spec => Termination /\ EventuallyReports /\ LeadsToResult
=============================================================================