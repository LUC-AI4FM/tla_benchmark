------------------------- MODULE MC_spanning -------------------------
(***************************************************************************)
(* Apalache-specific typed parameters and concrete sample values for the   *)
(* spanning-tree specification. The algorithm itself is defined inline     *)
(* rather than imported via INSTANCE spanning, so that this module can be  *)
(* parsed standalone.                                                      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Set(Int);
    Proc,
    \* @type: Int;
    NoPrnt,
    \* @type: Int;
    root,
    \* @type: Set(<<Int, Int>>);
    nbrs

VARIABLES
    \* @type: Int -> Int;
    prnt,
    \* @type: Int -> Bool;
    rpt,
    \* @type: Set(<<Int, Int>>);
    msg

vars == <<prnt, rpt, msg>>

(***************************************************************************)
(* Concrete sample values for the constants.                               *)
(***************************************************************************)
ProcVal == {1, 2, 3, 4}

NoPrntVal == 0

rootVal == 1

nbrsVal == { <<1, 2>>, <<2, 1>>,
             <<2, 3>>, <<3, 2>>,
             <<3, 4>>, <<4, 3>>,
             <<1, 4>>, <<4, 1>> }

(***************************************************************************)
(* The spanning-tree algorithm.                                            *)
(***************************************************************************)
Init ==
    /\ prnt = [i \in Proc |-> NoPrnt]
    /\ rpt = [i \in Proc |-> FALSE]
    /\ msg = {}

Update(i, j) ==
    /\ prnt[i] = NoPrnt
    /\ <<j, i>> \in msg
    /\ prnt' = [prnt EXCEPT ![i] = j]
    /\ UNCHANGED <<rpt, msg>>

Send(i) ==
    /\ (prnt[i] # NoPrnt) \/ (i = root)
    /\ ~rpt[i]
    /\ rpt' = [rpt EXCEPT ![i] = TRUE]
    /\ msg' = msg \cup { <<i, k>> : k \in { n \in Proc : <<i, n>> \in nbrs } }
    /\ UNCHANGED prnt

Next ==
    \E i \in Proc :
        \/ Send(i)
        \/ \E j \in Proc : Update(i, j)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ prnt \in [Proc -> Proc \cup {NoPrnt}]
    /\ rpt \in [Proc -> BOOLEAN]
    /\ msg \subseteq (Proc \X Proc)

=============================================================================