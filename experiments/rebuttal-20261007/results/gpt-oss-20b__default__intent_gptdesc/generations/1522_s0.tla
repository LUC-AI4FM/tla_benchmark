MODULE HuangTermination
EXTENDS Naturals, TLC

CONSTANTS N, Leader, MaxDenom

(* Process set *)
ProcSet == 1..N

VARIABLES localWeight, msgs, terminated

(* Helper functions *)
totalWeight ==
  (SUM p \in ProcSet : localWeight[p]) + (SUM m \in msgs : m[3])

(* Invariants *)
WeightConservation == totalWeight = MaxDenom
LocalWeightBounds == ∀ p \in ProcSet : 0 <= localWeight[p] /\ localWeight[p] <= MaxDenom
MsgWeightBounds == ∀ m \in msgs : 0 <= m[3] /\ m[3] <= MaxDenom

TerminatedInvariant ==
  terminated => (msgs = {} /\ localWeight[Leader] = MaxDenom /\ ∀ p \in ProcSet \ {Leader} : localWeight[p] = 0)

GlobalQuiescent == msgs = {} /\ ∀ p \in ProcSet \ {Leader} : localWeight[p] = 0

(* Actions *)
ReceiveMsg ==
  ∃ src, dst \in ProcSet, w \in Nat :
    <src,dst,w> \in msgs
    /\ w > 0
    /\ w <= MaxDenom
    /\ localWeight' = [localWeight EXCEPT ![dst] = @ + w]
    /\ msgs' = msgs \ {<src,dst,w>}
    /\ terminated' = terminated

Send ==
  ∃ p, q \in ProcSet, w \in Nat :
    p # q
    /\ localWeight[p] > 0
    /\ 0 < w <= localWeight[p]
    /\ localWeight' = [localWeight EXCEPT ![p] = @ - w]
    /\ msgs' = msgs ∪ {<p,q,w>}
    /\ terminated' = terminated

Idle ==
  ∃ p \in ProcSet :
    p # Leader
    /\ localWeight[p] > 0
    /\ localWeight' = [localWeight EXCEPT ![p] = 0]
    /\ msgs' = msgs ∪ {<p,Leader,localWeight[p]>}
    /\ terminated' = terminated

DetectTermination ==
  ¬terminated
  /\ localWeight[Leader] = MaxDen