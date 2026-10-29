---------------------------- MODULE MCYoYoNoPruning ----------------------------
(***************************************************************************)
(* Model-checking configuration for the Yo-Yo leader election algorithm  *)
(* without pruning. The YoYoNoPruning algorithm is written out inline     *)
(* below so that the module is self-contained.                            *)
(***************************************************************************)
EXTENDS Integers

(***************************************************************************)
(* Concrete network topology: 5 nodes, 5 undirected edges.                 *)
(***************************************************************************)
Nodes == 1 .. 5
Edges == {{1,2}, {1,5}, {2,3}, {2,5}, {3,4}}

(* Alternative, larger configuration: 11 nodes, 14 edges
Nodes == 1 .. 11
Edges == {{1,2}, {1,3}, {2,4}, {2,5}, {3,6}, {3,7}, {4,8}, {5,8},
          {5,9}, {6,9}, {6,10}, {7,10}, {8,11}, {10,11}}
*)

Neighbors(n) == {m \in Nodes : {m,n} \in Edges}

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

VARIABLES phase, incoming, outgoing, mailbox

vars == <<phase, incoming, outgoing, mailbox>>

(***************************************************************************)
(* Messages: "down" messages carry a candidate value, "up" messages carry  *)
(* a yes/no answer. Both record kinds have the same fields; unused fields  *)
(* hold dummy values.                                                      *)
(***************************************************************************)
Messages ==
    [type : {"down"}, sndr : Nodes, val : Nodes, ans : BOOLEAN]
  \cup [type : {"up"}, sndr : Nodes, val : Nodes, ans : BOOLEAN]

DownMsg(s, v) == [type |-> "down", sndr |-> s, val |-> v, ans |-> TRUE]
UpMsg(s, a)   == [type |-> "up", sndr |-> s, val |-> s, ans |-> a]

IsSource(n) == incoming[n] = {}

Init ==
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

(***************************************************************************)
(* Down phase: once values from all in-neighbors are present (immediately  *)
(* for a source), forward the minimum (own id for a source) to all         *)
(* out-neighbors. Received down messages are kept for the up phase.        *)
(***************************************************************************)
Down(n) ==
  /\ phase[n] = "down"
  /\ LET rcvd == {msg \in mailbox[n] : msg.type = "down" /\ msg.sndr \in incoming[n]}
         v    == IF incoming[n] = {} THEN n ELSE Min({msg.val : msg \in rcvd})
     IN  /\ {msg.sndr : msg \in rcvd} = incoming[n]
         /\ mailbox' = [m \in Nodes |->
                          IF m \in outgoing[n]
                          THEN mailbox[m] \cup {DownMsg(n, v)}
                          ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

(***************************************************************************)
(* Up phase: once replies from all out-neighbors are present (immediately  *)
(* for a sink), answer the in-neighbors and reverse the edges carrying a   *)
(* "no".                                                                   *)
(***************************************************************************)
Up(n) ==
  /\ phase[n] = "up"
  /\ LET downs    == {msg \in mailbox[n] : msg.type = "down" /\ msg.sndr \in incoming[n]}
         ups      == {msg \in mailbox[n] : msg.type = "up" /\ msg.sndr \in outgoing[n]}
         noSndrs  == {u.sndr : u \in {w \in ups : ~ w.ans}}
         allYes   == noSndrs = {}
         v        == IF downs = {} THEN n ELSE Min({d.val : d \in downs})
         yesTo    == IF allYes
                     THEN {d.sndr : d \in {e \in downs : e.val = v}}
                     ELSE {}
         noTo     == incoming[n] \ yesTo
     IN  /\ {u.sndr : u \in ups} = outgoing[n]
         /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ (downs \cup ups)
                          ELSE IF m \in incoming[n]
                               THEN mailbox[m] \cup {UpMsg(n, m \in yesTo)}
                               ELSE mailbox[m]]
         /\ incoming' = [incoming EXCEPT ![n] = (@ \ noTo) \cup noSndrs]
         /\ outgoing' = [outgoing EXCEPT ![n] = (@ \ noSndrs) \cup noTo]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Next == \E n \in Nodes : Down(n) \/ Up(n)

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(Down(n) \/ Up(n))

(***************************************************************************)
(* Invariants and properties.                                              *)
(***************************************************************************)
TypeOK ==
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]

NeighborInv ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] = Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}

NoNewSource ==
  [][\A n \in Nodes : ~ IsSource(n) => incoming'[n] # {}]_vars

Liveness ==
  <>[](\E n \in Nodes : \A m \in Nodes : IsSource(m) <=> m = n)

=============================================================================