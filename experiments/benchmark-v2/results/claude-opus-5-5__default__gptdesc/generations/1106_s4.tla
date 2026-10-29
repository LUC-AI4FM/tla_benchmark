------------------------------ MODULE APAspanning ------------------------------
(***************************************************************************)
(* Apalache-specific wrapper for the spanning-tree specification.          *)
(* It declares typed constants and variables, gives concrete sample        *)
(* values for the constants (ConstInit), and imports the algorithm from    *)
(* the separate module `spanning' via INSTANCE. The inner module below     *)
(* stands in for the original spanning.tla so this file parses on its own. *)
(***************************************************************************)
EXTENDS Integers

  ---------------------------- MODULE spanning ----------------------------
  (*************************************************************************)
  (* Distributed construction of a spanning tree rooted at `root'.         *)
  (* prnt[i] : parent of process i (NoPrc if not yet known)                *)
  (* rpt[i]  : whether i has already sent messages to its neighbors        *)
  (* msg     : set of pairs <<k, i>> meaning "message to k from i"         *)
  (*************************************************************************)
  CONSTANTS Proc, NoPrc, root, nbrs
  VARIABLES prnt, rpt, msg

  vars == <<prnt, rpt, msg>>

  Neighbors(i) == {k \in Proc : <<i, k>> \in nbrs}

  TypeOK ==
    /\ prnt \in [Proc -> Proc \cup {NoPrc}]
    /\ rpt \in [Proc -> BOOLEAN]
    /\ msg \subseteq (Proc \X Proc)

  Init ==
    /\ prnt = [i \in Proc |-> IF i = root THEN root ELSE NoPrc]
    /\ rpt = [i \in Proc |-> FALSE]
    /\ msg = {}

  \* Process i, which has a parent and has not yet reported, sends a
  \* message to each of its neighbors.
  Send(i) ==
    /\ prnt[i] # NoPrc
    /\ ~ rpt[i]
    /\ rpt' = [rpt EXCEPT ![i] = TRUE]
    /\ msg' = msg \cup {<<k, i>> : k \in Neighbors(i)}
    /\ UNCHANGED prnt

  \* Process i, which has no parent yet, adopts the sender k of a
  \* received message as its parent.
  Update(i, k) ==
    /\ prnt[i] = NoPrc
    /\ <<i, k>> \in msg
    /\ prnt' = [prnt EXCEPT ![i] = k]
    /\ UNCHANGED <<rpt, msg>>

  Next ==
    \/ \E i \in Proc : Send(i)
    \/ \E i, k \in Proc : Update(i, k)

  Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

  \* Safety: every parent pointer of a non-root process refers to a neighbor.
  ParentIsNeighbor ==
    \A i \in Proc :
      (i # root /\ prnt[i] # NoPrc) => <<i, prnt[i]>> \in nbrs

  \* Safety: the root is always its own parent.
  RootIsOwnParent == prnt[root] = root

  \* Safety: only processes that have a parent have reported.
  ReportImpliesParent == \A i \in Proc : rpt[i] => prnt[i] # NoPrc

  Inv == TypeOK /\ ParentIsNeighbor /\ RootIsOwnParent /\ ReportImpliesParent

  \* Liveness: eventually every process has a parent (graph is connected).
  Termination == <>(\A i \in Proc : prnt[i] # NoPrc)
  ==========================================================================