---------------------------- MODULE MC_spanning ----------------------------
(***************************************************************************)
(* Apalache-compatible model of a spanning tree construction algorithm.   *)
(* The algorithm of the `spanning' module is inlined here, so this module *)
(* parses without any other files.                                         *)
(*                                                                         *)
(* Processes build a spanning tree rooted at `root'. A process with no    *)
(* parent that receives a message from neighbor j adopts j as its parent. *)
(* It then forwards messages to its other neighbors. A process that has   *)
(* a parent may report.                                                    *)
(*                                                                         *)
(* No fairness conditions are used, since Apalache cannot handle weak     *)
(* fairness.                                                               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Proc,
    \* @type: Str;
    NoPrnt,
    \* @type: Str;
    root,
    \* @type: Set(<<Str, Str>>);
    nbrs

VARIABLES
    \* @type: Str -> Str;
    prnt,
    \* @type: Str -> Bool;
    rpt,
    \* @type: Set(<<Str, Str>>);
    msg

vars == <<prnt, rpt, msg>>

\* Concrete constant values: three processes connected linearly.
ProcVal == {"p1", "p2", "p3"}

NoPrntVal == "NoPrnt"

rootVal == "p1"

nbrsVal == {<<"p1", "p2">>, <<"p2", "p1">>,
            <<"p2", "p3">>, <<"p3", "p2">>}

\* Neighbors of process i.
Nbrs(i) == {j \in Proc : <<i, j>> \in nbrs}

-----------------------------------------------------------------------------
(* The spanning tree algorithm *)

Init ==
    /\ prnt = [i \in Proc |-> IF i = root THEN root ELSE NoPrnt]
    /\ rpt  = [i \in Proc |-> FALSE]
    /\ msg  = {<<root, k>> : k \in Nbrs(root)}

\* Process i receives a message from neighbor j and adopts j as its parent.
Update(i, j) ==
    /\ prnt[i] = NoPrnt
    /\ <<j, i>> \in msg
    /\ prnt' = [prnt EXCEPT ![i] = j]
    /\ msg'  = msg \cup {<<i, k>> : k \in Nbrs(i) \ {j}}
    /\ UNCHANGED rpt

\* Process i, which already has a parent, reports.
Parent(i) ==
    /\ prnt[i] /= NoPrnt
    /\ ~rpt[i]
    /\ rpt' = [rpt EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<prnt, msg>>

Next ==
    \/ \E i \in Proc, j \in Proc : Update(i, j)
    \/ \E i \in Proc : Parent(i)

\* No fairness, for Apalache compatibility.
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ prnt \in [Proc -> Proc \cup {NoPrnt}]
    /\ rpt \in [Proc -> BOOLEAN]
    /\ msg \subseteq Proc \X Proc

=============================================================================