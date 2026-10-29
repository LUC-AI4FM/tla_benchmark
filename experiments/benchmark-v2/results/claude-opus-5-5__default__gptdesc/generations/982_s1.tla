------------------------------ MODULE MCYoYoNoPruning ------------------------------
(***************************************************************************)
(* Model-checking wrapper around the YoYoNoPruning specification.          *)
(* The graph is fixed in this module.  The algorithm itself (Init, Next,   *)
(* Spec) comes from the instantiated YoYoNoPruning module, which is        *)
(* included here as a submodule so that this file is self-contained.       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

  ----------------------------- MODULE YoYoNoPruning -----------------------------
  (*************************************************************************)
  (* The Yo-Yo leader election algorithm without the pruning step.         *)
  (* Edges are initially oriented from smaller to larger node identities.  *)
  (* In the "down" phase, sources send their identity downward, and every  *)
  (* other node forwards the smallest value it received.  In the "up"      *)
  (* phase, sinks and then internal nodes reply "yes" or "no" upward, and  *)
  (* the edges along which "no" was sent are reversed.                     *)
  (*************************************************************************)
  CONSTANTS Nodes, Edges

  ASSUME /\ Nodes \subseteq Nat
         /\ \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2

  VARIABLES phase, incoming, outgoing, mailbox

  vars == <<phase, incoming, outgoing, mailbox>>

  Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

  Min(S) == CHOOSE x \in S : \A y \in S : x <= y

  DownMsg(snd, v) == [phase |-> "down", sndr |-> snd, val |-> v]
  UpMsg(snd, r)   == [phase |-> "up", sndr |-> snd, reply |-> r]

  Messages == [phase : {"down"}, sndr : Nodes, val : Nodes]
              \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

  TypeOK ==
    /\ phase \in [Nodes -> {"down", "up"}]
    /\ incoming \in [Nodes -> SUBSET Nodes]
    /\ outgoing \in [Nodes -> SUBSET Nodes]
    /\ mailbox \in [Nodes -> SUBSET Messages]

  Init ==
    /\ phase = [n \in Nodes |-> "down"]
    /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
    /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
    /\ mailbox = [n \in Nodes |-> {}]

  (* A source starts the down phase by sending its own identity. *)
  DownSource(n) ==
    /\ phase[n] = "down"
    /\ incoming[n] = {}
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ mailbox' = [m \in Nodes |->
                     IF m \in outgoing[n]
                     THEN mailbox[m] \cup {DownMsg(n, n)}
                     ELSE mailbox[m]]
    /\ UNCHANGED <<incoming, outgoing>>

  (* A non-source node forwards the minimum value received from all       *)
  (* in-neighbors.  The down messages are kept for use in the up phase.   *)
  DownOther(n) ==
    /\ phase[n] = "down"
    /\ incoming[n] # {}
    /\ LET downs == {msg \in mailbox[n] : msg.phase = "down"}
       IN  /\ {msg.sndr : msg \in downs} = incoming[n]
           /\ LET minVal == Min({msg.val : msg \in downs})
              IN  mailbox' = [m \in Nodes |->
                                IF m \in outgoing[n]
                                THEN mailbox[m] \cup {DownMsg(n, minVal)}
                                ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing>>

  (* A source collects the replies of its out-neighbors and reverses      *)
  (* the edges along which it received "no".                              *)
  UpSource(n) ==
    /\ phase[n] = "up"
    /\ incoming[n] = {}
    /\ LET ups == {msg \in mailbox[n] : msg.phase = "up"}
           noRcvd == {msg.sndr : msg \in {u \in ups : u.reply = "no"}}
       IN  /\ {msg.sndr : msg \in ups} = outgoing[n]
           /\ phase' = [phase EXCEPT ![n] = "down"]
           /\ incoming' = [incoming EXCEPT ![n] = noRcvd]
           /\ outgoing' = [outgoing EXCEPT ![n] = @ \ noRcvd]
           /\ mailbox' = [mailbox EXCEPT ![n] = @ \ ups]

  (* A non-source node, once all out-neighbors replied (vacuous for       *)
  (* sinks), replies to its in-neighbors and reverses edges with "no".    *)
  UpOther(n) ==
    /\ phase[n] = "up"
    /\ incoming[n] # {}
    /\ LET downs == {msg \in mailbox[n] : msg.phase = "down"}
           ups   == {msg \in mailbox[n] : msg.phase = "up"}
       IN  /\ {msg.sndr : msg \in downs} = incoming[n]
           /\ {msg.sndr : msg \in ups} = outgoing[n]
           /\ LET minVal == Min({msg.val : msg \in downs})
                  noRcvd == {msg.sndr : msg \in {u \in ups : u.reply = "no"}}
                  yesTo  == IF noRcvd = {}
                            THEN {msg.sndr : msg \in {d \in downs : d.val = minVal}}
                            ELSE {}
                  noTo   == incoming[n] \ yesTo
              IN  /\ phase' = [phase EXCEPT ![n] = "down"]
                  /\ incoming' = [incoming EXCEPT ![n] = (@ \ noTo) \cup noRcvd]
                  /\ outgoing' = [outgoing EXCEPT ![n] = (@ \ noRcvd) \cup noTo]
                  /\ mailbox' =
                       [m \in Nodes |->
                          IF m = n
                          THEN mailbox[n] \ (downs \cup ups)
                          ELSE IF m \in incoming[n]
                               THEN mailbox[m] \cup
                                      {UpMsg(n, IF m \in yesTo THEN "yes" ELSE "no")}
                               ELSE mailbox[m]]

  (* Reversal of an edge on the receiving side of a "no" reply is handled *)
  (* when the receiver processes its up messages (UpSource / UpOther).    *)

  Next == \E n \in Nodes :
            \/ DownSource(n)
            \/ DownOther(n)
            \/ UpSource(n)
            \/ UpOther(n)

  Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
  ================================================================================