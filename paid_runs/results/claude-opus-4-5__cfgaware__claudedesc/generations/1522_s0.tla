---------------------------- MODULE Huang ----------------------------
EXTENDS Integers, Sequences, FiniteSets, Reals

CONSTANTS Procs, Leader

ASSUME Leader \in Procs

VARIABLES weight, active, queue

vars == <<weight, active, queue>>

-----------------------------------------------------------------------------
(* Dyadic rationals represented as pairs <<numerator, denominator>> where
   denominator is a power of 2. We use integers for simplicity. *)

(* Weight is represented as a pair <<n, d>> meaning n/d *)

WeightType == {<<n, d>> \in (Int \X Int) : d > 0}

Zero == <<0, 1>>
One == <<1, 1>>

(* Add two weights *)
AddWeight(w1, w2) ==
    LET n1 == w1[1] * w2[2] + w2[1] * w1[2]
        d == w1[2] * w2[2]
    IN <<n1, d>>

(* Halve a weight *)
HalfWeight(w) == <<w[1], w[2] * 2>>

(* Check if weight equals one *)
IsOne(w) == w[1] = w[2]

(* Check if weight is zero *)
IsZero(w) == w[1] = 0

(* Sum of a set of weights *)
RECURSIVE SumWeightSet(_)
SumWeightSet(S) ==
    IF S = {} THEN Zero
    ELSE LET w == CHOOSE x \in S : TRUE
         IN AddWeight(w, SumWeightSet(S \ {w}))

(* Sum weights in a sequence *)
RECURSIVE SumWeightSeq(_)
SumWeightSeq(s) ==
    IF s = <<>> THEN Zero
    ELSE AddWeight(Head(s), SumWeightSeq(Tail(s)))

(* Total weight of all messages in all queues *)
TotalQueueWeight ==
    LET AllQueueWeights == UNION {ToSet(queue[p]) : p \in Procs}
        ToSet(s) == {s[i] : i \in 1..Len(s)}
    IN SumWeightSet(AllQueueWeights)

(* Helper to convert sequence to set *)
SeqToSet(s) == {s[i] : i \in 1..Len(s)}

(* Total queue weight computed properly *)
TotalMsgWeight ==
    LET QueueSum(p) == SumWeightSeq(queue[p])
    IN SumWeightSet({QueueSum(p) : p \in Procs})

(* Total process weight *)
TotalProcWeight == SumWeightSet({weight[p] : p \in Procs})

(* Weight conservation: sum of all weights equals 1 *)
WeightConservation ==
    LET total == AddWeight(TotalProcWeight, TotalMsgWeight)
    IN total[1] * 1 = total[2] * 1  \* n/d = 1 means n = d

-----------------------------------------------------------------------------
(* Type invariant *)
TypeOK ==
    /\ weight \in [Procs -> WeightType]
    /\ active \in [Procs -> BOOLEAN]
    /\ queue \in [Procs -> Seq(WeightType)]
    /\ WeightConservation

-----------------------------------------------------------------------------
(* Initial state *)
Init ==
    /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
    /\ active = [p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE]
    /\ queue = [p \in Procs |-> <<>>]

-----------------------------------------------------------------------------
(* Actions *)

(* Send: an active process sends a message by halving its weight *)
Send(p, q) ==
    /\ p \in Procs
    /\ q \in Procs
    /\ p # q
    /\ active[p]
    /\ ~IsZero(weight[p])
    /\ weight' = [weight EXCEPT ![p] = HalfWeight(@)]
    /\ queue' = [queue EXCEPT ![q] = Append(@, HalfWeight(weight[p]))]
    /\ UNCHANGED active

(* Receive for non-leader: becomes active and adds weight *)
Rcv(p) ==
    /\ p \in Procs
    /\ p # Leader
    /\ Len(queue[p]) > 0
    /\ LET msg == Head(queue[p])
       IN /\ weight' = [weight EXCEPT ![p] = AddWeight(@, msg)]
          /\ active' = [active EXCEPT ![p] = TRUE]
          /\ queue' = [queue EXCEPT ![p] = Tail(@)]

(* Idle for non-leader: sends weight back to leader and becomes inactive *)
Idle(p) ==
    /\ p \in Procs
    /\ p # Leader
    /\ active[p]
    /\ ~IsZero(weight[p])
    /\ queue' = [queue EXCEPT ![Leader] = Append(@, weight[p])]
    /\ weight' = [weight EXCEPT ![p] = Zero]
    /\ active' = [active EXCEPT ![p] = FALSE]

(* Leader becomes inactive *)
IdleLdr ==
    /\ active[Leader]
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED <<weight, queue>>

(* Leader receives weight without reactivating *)
RcvLdr ==
    /\ Len(queue[Leader]) > 0
    /\ LET msg == Head(queue[Leader])
       IN /\ weight' = [weight EXCEPT ![Leader] = AddWeight(@, msg)]
          /\ queue' = [queue EXCEPT ![Leader] = Tail(@)]
    /\ UNCHANGED active

-----------------------------------------------------------------------------
(* Next state relation *)
Next ==
    \/ \E p, q \in Procs : Send(p, q)
    \/ \E p \in Procs \ {Leader} : Rcv(p)
    \/ \E p \in Procs \ {Leader} : Idle(p)
    \/ IdleLdr
    \/ RcvLdr

-----------------------------------------------------------------------------
(* Fairness conditions *)
Fairness ==
    /\ \A p \in Procs \ {Leader} : WF_vars(Rcv(p))
    /\ \A p \in Procs \ {Leader} : WF_vars(Idle(p))
    /\ WF_vars(RcvLdr)
    /\ WF_vars(IdleLdr)

-----------------------------------------------------------------------------
(* Specification *)
Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Termination detection: Leader is inactive and holds weight 1 *)
Detected == ~active[Leader] /\ IsOne(weight[Leader])

(* Actual termination: all processes inactive and all queues empty *)
Terminated ==
    /\ \A p \in Procs : ~active[p]
    /\ \A p \in Procs : queue[p] = <<>>

-----------------------------------------------------------------------------
(* Safety: if termination is detected, then system is terminated *)
Safe == Detected => Terminated

(* Liveness: actual termination leads to detection *)
Live == Terminated ~> Detected

-----------------------------------------------------------------------------
(* Theorems *)
THEOREM Spec => []Safe

THEOREM Spec => Live

-----------------------------------------------------------------------------
(* State constraint for model checking: bound denominator growth *)
MaxDenom == 1024

StateConstraint ==
    /\ \A p \in Procs : weight[p][2] <= MaxDenom
    /\ \A p \in Procs : \A i \in 1..Len(queue[p]) : queue[p][i][2] <= MaxDenom

=============================================================================