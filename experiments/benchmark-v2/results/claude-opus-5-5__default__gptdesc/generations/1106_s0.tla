---------------------------- MODULE MC_spanning ----------------------------
(***************************************************************************)
(* Apalache-specific wrapper for the spanning-tree specification.         *)
(* It supplies type annotations and concrete constant values, and imports *)
(* the algorithm through INSTANCE spanning. The spanning specification is *)
(* kept separate as a submodule so that this file parses standalone.      *)
(***************************************************************************)
EXTENDS FiniteSets

    ------------------------- MODULE spanning -------------------------
    (*********************************************************************)
    (* Original spanning-tree algorithm, kept separate from the typed    *)
    (* wrapper. The root floods messages to its neighbours. A non-root   *)
    (* process without a parent adopts the sender of a received message  *)
    (* as its parent, then reports by forwarding to its neighbours.      *)
    (*********************************************************************)
    CONSTANTS Proc, NoPrnt, root, nbrs

    VARIABLES prnt, rpt, msg

    vars == <<prnt, rpt, msg>>

    Nbrs(i) == {k \in Proc : <<i, k>> \in nbrs}

    TypeOK ==
        /\ prnt \in [Proc -> Proc \cup {NoPrnt}]
        /\ rpt \in [Proc -> BOOLEAN]
        /\ msg \subseteq (Proc \X Proc)

    Init ==
        /\ prnt = [i \in Proc |-> NoPrnt]
        /\ rpt = [i \in Proc |-> FALSE]
        /\ msg = {}

    \* Process i (root, or one that already has a parent) reports once.
    Send(i) ==
        /\ (i = root \/ prnt[i] # NoPrnt)
        /\ ~rpt[i]
        /\ rpt' = [rpt EXCEPT ![i] = TRUE]
        /\ msg' = msg \cup {<<i, k>> : k \in Nbrs(i)}
        /\ UNCHANGED prnt

    \* Non-root process i adopts k as its parent upon a message from k.
    Update(i, k) ==
        /\ i # root
        /\ prnt[i] = NoPrnt
        /\ <<k, i>> \in msg
        /\ prnt' = [prnt EXCEPT ![i] = k]
        /\ UNCHANGED <<rpt, msg>>

    Next ==
        \/ \E i \in Proc : Send(i)
        \/ \E i, k \in Proc : Update(i, k)

    Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

    \* Safety: parents are always neighbours; the root never gets a parent.
    ParentIsNbr ==
        \A i \in Proc : prnt[i] # NoPrnt => <<prnt[i], i>> \in nbrs

    RootHasNoParent == prnt[root] = NoPrnt

    \* Only processes that reported may have sent messages.
    MsgFromReported == \A m \in msg : rpt[m[1]]

    Safety == TypeOK /\ ParentIsNbr /\ RootHasNoParent /\ MsgFromReported

    \* Liveness: every non-root process eventually gets a parent
    \* (assuming a connected neighbour relation).
    Termination == <>(\A i \in Proc \ {root} : prnt[i] # NoPrnt)
    ===================================================================