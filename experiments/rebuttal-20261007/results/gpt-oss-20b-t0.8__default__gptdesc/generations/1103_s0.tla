MODULE NBAC
EXTENDS Naturals

CONSTANT N

VARIABLES state, vote, crashed, msgs, fd

(* Types *)
StateSet == {"init","voting","decidedCommit","decidedAbort","crashed"}
VoteSet  == {"YES","NO","none"}

Init ==
  /\ state = [i \in 1..N |-> "init"]
  /\ vote  = [i \in 1..N |-> "none"]
  /\ crashed = [i \in 1..N |-> FALSE]
  /\ msgs   = {}
  /\ fd     = [i \in 1..N |-> [j \in 1..N |-> FALSE]]

(* Actions *)
VoteAction(i) ==
  LET v ∈ {"YES","NO"} IN
    /\ state[i] = "init"
    /\ ~crashed[i]
    /\ UNCHANGED <<msgs, fd>>
    /\ state' = [state EXCEPT ![i] = "voting"]
    /\ vote'  = [vote  EXCEPT ![i] = v]

SendVote(i,j) ==
  /\ i ∈ 1..N
  /\ j ∈ 1..N
  /\ i # j
  /\ ~crashed[i]
  /\ state[i] = "voting"
  /\ msgs'   = msgs \cup { [from |-> i, to |-> j, type |-> "VoteMsg", vote |-> vote[i]] }
  /\ UNCHANGED <<state, vote, crashed, fd>>

ReceiveVote(i) ==
  \E m ∈ msgs :
    /\ m.to = i
    /\ m.type = "VoteMsg"
    /\ msgs'   = msgs \ {m}
    /\ UNCHANGED <<state, vote, crashed, fd>>

CrashAction(i) ==
  /\ ~crashed[i]
  /\ crashed' = [crashed EXCEPT ![i] = TRUE]
  /\ state'   = [state EXCEPT ![i] = "crashed"]
  /\ UNCHANGED <<vote, msgs, fd>>

FDUpdate(i,j) ==
  LET b ∈ {TRUE, FALSE} IN
    /\ i ∈ 1..N
    /\ j ∈ 1..N
    /\ UNCHANGED <<state, vote, crashed, msgs>>
    /\ fd' = [fd EXCEPT ![i][j] = b]

DecisionCommit(i) ==
  /\ state[i] = "voting"
  /\ ~crashed[i]
  /\ \A j ∈ 1..N : (j # i) => (crashed[j] \/ vote[j] = "YES")
  /\ state' = [state EXCEPT ![i] = "decidedCommit"]
  /\ UNCHANGED <<vote, crashed, msgs, fd>>

DecisionAbort(i) ==
  /\ state[i] = "voting"
  /\ ~crashed[i]
  /\ \E j ∈ 1..N : (j # i) /\ vote[j] = "NO"
  /\ state' = [state EXCEPT ![i] = "decidedAbort"]
  /\ UNCHANGED <<vote, crashed, msgs, fd>>

Next ==
  (\E i ∈ 1..N :
     VoteAction(i)
   \/ DecisionCommit(i)
   \/ DecisionAbort(i)
   \/ CrashAction(i)
   \/ ReceiveVote(i))
  \/ \E i ∈ 1..N, j ∈ 1..N : SendVote(i,j)
  \/ \E i ∈ 1..N, j ∈ 1..N : FDUpdate(i,j)

Spec == Init /\ [][Next]_<<state, vote, crashed, msgs, fd>>

(* Invariants *)
TypeCorrectness ==
  /\ state ∈ [1..N -> StateSet]
  /\ vote  ∈ [1..N -> VoteSet]
  /\ crashed ∈ [1..N -> BOOLEAN]
  /\ msgs ⊆ { [from: 1..N, to: 1..N, type: "VoteMsg", vote: {"YES","NO"}] }
  /\ fd   ∈ [1..N -> [1..N -> BOOLEAN]]

ValidityInvariant ==
  \A i ∈ 1..N :
    (crashed[i] \/ vote[i]="YES") => state[i] = "decidedCommit" \/ state[i]="voting"

UnanimousYesImpliesCommit ==
  []( (\A i ∈ 1..N : ~crashed[i] => vote[i]="YES")
     => <> (\A i ∈ 1..N : state[i]="decidedCommit"))

============================================================================