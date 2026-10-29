---------------------------- MODULE MC_spanning ----------------------------
(***************************************************************************)
(* Apalache wrapper for the spanning-tree specification `spanning`.        *)
(* It supplies type annotations for the constants and variables, and       *)
(* concrete constant values through ConstInit. The algorithm, its          *)
(* invariants and its liveness properties stay in module `spanning`.       *)
(*                                                                         *)
(* So that this file parses with SANY on its own, `spanning` is written    *)
(* here as an inner module. It is self-contained and is only used through  *)
(* INSTANCE.                                                               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

  ------------------------------ MODULE spanning ------------------------------
  EXTENDS Integers, FiniteSets

  CONSTANTS
      Proc,     \* the set of processes
      root,     \* the distinguished root process
      nadir,    \* the "no parent" value
      nbrs      \* the neighbor relation, a set of pairs <<i, j>>

  ASSUME root \in Proc
  ASSUME nadir \notin Proc
  ASSUME nbrs \subseteq (Proc \X Proc)

  VARIABLES
      prnt,     \* prnt[i]: parent of process i, or nadir
      rpt,      \* rpt[i]: TRUE once process i has reported to its parent
      msg       \* the set of messages in transit, as pairs <<from, to>>

  vars == <<prnt, rpt, msg>>

  Nbrs(i) == { j \in Proc : <<i, j>> \in nbrs }

  TypeOK ==
      /\ prnt \in [Proc -> Proc \cup {nadir}]
      /\ rpt \in [Proc -> BOOLEAN]
      /\ msg \subseteq (Proc \X Proc)

  Init ==
      /\ prnt = [i \in Proc |-> IF i = root THEN root ELSE nadir]
      /\ rpt = [i \in Proc |-> FALSE]
      /\ msg = { <<root, j>> : j \in Nbrs(root) }

  \* Process i receives a message from j while it has no parent yet.
  \* It adopts j as its parent and forwards the message to its other
  \* neighbors.
  Adopt(i, j) ==
      /\ <<j, i>> \in msg
      /\ prnt[i] = nadir
      /\ prnt' = [prnt EXCEPT ![i] = j]
      /\ msg' = (msg \ {<<j, i>>}) \cup { <<i, k>> : k \in Nbrs(i) \ {j} }
      /\ UNCHANGED rpt

  \* Process i already has a parent, so it discards the message from j.
  Discard(i, j) ==
      /\ <<j, i>> \in msg
      /\ prnt[i] # nadir
      /\ msg' = msg \ {<<j, i>>}
      /\ UNCHANGED <<prnt, rpt>>

  \* A non-root process with a parent reports to that parent.
  Report(i) ==
      /\ i # root
      /\ prnt[i] # nadir
      /\ ~rpt[i]
      /\ rpt' = [rpt EXCEPT ![i] = TRUE]
      /\ UNCHANGED <<prnt, msg>>

  Next ==
      \/ \E i \in Proc, j \in Proc : Adopt(i, j) \/ Discard(i, j)
      \/ \E i \in Proc : Report(i)

  Fairness ==
      /\ \A i \in Proc, j \in Proc : WF_vars(Adopt(i, j))
      /\ \A i \in Proc, j \in Proc : WF_vars(Discard(i, j))
      /\ \A i \in Proc : WF_vars(Report(i))

  Spec == Init /\ [][Next]_vars /\ Fairness

  (* Safety: every assigned parent is a neighbor, and only processes  *)
  (* with a parent may report.                                         *)
  ParentIsNeighbor ==
      \A i \in Proc \ {root} : prnt[i] # nadir => <<i, prnt[i]>> \in nbrs

  ReportImpliesParent ==
      \A i \in Proc : rpt[i] => prnt[i] # nadir

  RootIsOwnParent == prnt[root] = root

  Safety == TypeOK /\ ParentIsNeighbor /\ ReportImpliesParent /\ RootIsOwnParent

  (* Liveness: on a connected graph, every process gets a parent and  *)
  (* every non-root process eventually reports.                        *)
  AllHaveParents == <>(\A i \in Proc : prnt[i] # nadir)

  AllReported == <>(\A i \in Proc \ {root} : rpt[i])

  Liveness == AllHaveParents /\ AllReported
  =============================================================================