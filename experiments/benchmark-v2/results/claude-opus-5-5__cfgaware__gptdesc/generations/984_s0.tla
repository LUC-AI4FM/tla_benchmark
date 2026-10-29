---------------------------- MODULE YoYoPruning ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N
ASSUME N \in Nat \ {0}

Nodes == 1 .. N

VARIABLES active, phase, incoming, outgoing, mailbox
vars == <<active, phase, incoming, outgoing, mailbox>>

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(***************************************************************************)
(* Graph-related definitions                                              *)
(***************************************************************************)
Edges == {e \in SUBSET Nodes : Cardinality(e) = 2}

RECURSIVE Reach(_, _)
Reach(S, E) ==
  LET S2 == S \cup {n \in Nodes : \E m \in S : {m, n} \in E}
  IN  IF S2 = S THEN S ELSE Reach(S2, E)

Connected(E) == Reach({1}, E) = Nodes

(***************************************************************************)
(* Messages                                                               *)
(***************************************************************************)
downMsg(s, v) == [phs |-> "down", sndr |-> s, val |-> v]
upMsg(s, r, p) == [phs |-> "up", sndr |-> s, reply |-> r, prune |-> p]

Messages ==
     [phs : {"down"}, sndr : Nodes, val : Nodes]
  \cup [phs : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]

(***************************************************************************)
(* Initial states                                                         *)
(***************************************************************************)
Init ==
  /\ \E E \in SUBSET Edges :
        /\ Connected(E)
        /\ incoming = [n \in Nodes |-> {m \in Nodes : {m, n} \in E /\ m < n}]
        /\ outgoing = [n \in Nodes |-> {m \in Nodes : {m, n} \in E /\ m > n}]
  /\ active = [n \in Nodes |-> TRUE]
  /\ phase = [n \in Nodes |-> "down"]
  /\ mailbox = [n \in Nodes |-> {}]

(***************************************************************************)
(* Down phase                                                             *)
(***************************************************************************)
DownSource(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] = {}
  /\ outgoing[n] # {}
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n] THEN mailbox[m] \cup {downMsg(n, n)}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

DownOther(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] # {}
  /\ LET dmsgs == {msg \in mailbox[n] : msg.phs = "down"}
         min   == Min({msg.val : msg \in dmsgs})
     IN  /\ {msg.sndr : msg \in dmsgs} = incoming[n]
         /\ mailbox' = [m \in Nodes |->
                          IF m \in outgoing[n] THEN mailbox[m] \cup {downMsg(n, min)}
                          ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(***************************************************************************)
(* Up phase                                                               *)
(***************************************************************************)
UpSource(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ incoming[n] = {}
  /\ outgoing[n] # {}
  /\ LET umsgs == {msg \in mailbox[n] : msg.phs = "up"}
         noOut == {u.sndr : u \in {v \in umsgs : v.reply = "no"}}
         prOut == {u.sndr : u \in {v \in umsgs : v.prune}}
     IN  /\ {u.sndr : u \in umsgs} = outgoing[n]
         /\ incoming' = [incoming EXCEPT ![n] = noOut \ prOut]
         /\ outgoing' = [outgoing EXCEPT ![n] = outgoing[n] \ (noOut \cup prOut)]
  /\ mailbox' = [mailbox EXCEPT ![n] = {}]
  /\ phase' = [phase EXCEPT ![n] = "down"]
  /\ UNCHANGED active

UpOther(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ incoming[n] # {}
  /\ LET dmsgs   == {msg \in mailbox[n] : msg.phs = "down"}
         umsgs   == {msg \in mailbox[n] : msg.phs = "up"}
         vals    == {d.val : d \in dmsgs}
         min     == Min(vals)
         noOut   == {u.sndr : u \in {v \in umsgs : v.reply = "no"}}
         prOut   == {u.sndr : u \in {v \in umsgs : v.prune}}
         keepers == {Min({d.sndr : d \in {e \in dmsgs : e.val = v}}) : v \in vals}
         leaf    == (outgoing[n] \ prOut = {}) /\ Cardinality(vals) = 1
         Val(s)  == (CHOOSE d \in dmsgs : d.sndr = s).val
         Yes(s)  == noOut = {} /\ Val(s) = min
         Pr(s)   == leaf \/ s \notin keepers
     IN  /\ {u.sndr : u \in umsgs} = outgoing[n]
         /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN {}
                          ELSE IF m \in incoming[n]
                               THEN mailbox[m] \cup
                                      {upMsg(n, IF Yes(m) THEN "yes" ELSE "no", Pr(m))}
                               ELSE mailbox[m]]
         /\ active' = [active EXCEPT ![n] = ~leaf]
         /\ incoming' = [incoming EXCEPT ![n] =
               IF leaf THEN {}
               ELSE {s \in incoming[n] : Yes(s) /\ ~Pr(s)} \cup (noOut \ prOut)]
         /\ outgoing' = [outgoing EXCEPT ![n] =
               IF leaf THEN {}
               ELSE (outgoing[n] \ (noOut \cup prOut))
                      \cup {s \in incoming[n] : ~Yes(s) /\ ~Pr(s)}]
  /\ phase' = [phase EXCEPT ![n] = "down"]

(***************************************************************************)
(* Next-state relation and specification                                  *)
(***************************************************************************)
Next == \E n \in Nodes :
          \/ DownSource(n)
          \/ DownOther(n)
          \/ UpSource(n)
          \/ UpOther(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Properties                                                             *)
(***************************************************************************)
TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]

NeighborInv ==
  \A n \in Nodes :
     /\ n \notin incoming[n] \cup outgoing[n]
     /\ incoming[n] \cap outgoing[n] = {}
     /\ ~active[n] => (incoming[n] = {} /\ outgoing[n] = {})

Finished ==
  \A n \in Nodes : active[n] => (incoming[n] = {} /\ outgoing[n] = {})

FinishIffTerminated == Finished <=> ~(ENABLED Next)

Liveness == <>Finished

=============================================================================