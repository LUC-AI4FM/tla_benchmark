---------------------------- MODULE APAspanning ----------------------------
(***************************************************************************)
(* Apalache-compatible type annotations for the spanning tree algorithm.  *)
(* The underlying algorithm is given in the module `spanning', included    *)
(* here as a submodule so that this file parses on its own.                *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

    ---------------------------- MODULE spanning ----------------------------
    EXTENDS Integers, FiniteSets

    CONSTANTS Proc, NoPrnt, root, nbrs

    ASSUME /\ NoPrnt \notin Proc
           /\ root \in Proc
           /\ nbrs \subseteq Proc \X Proc

    VARIABLES prnt, rpt, msg

    vars == <<prnt, rpt, msg>>

    TypeOK == /\ prnt \in [Proc -> Proc \cup {NoPrnt}]
              /\ rpt \in [Proc -> BOOLEAN]
              /\ msg \subseteq Proc \X Proc

    Init == /\ prnt = [i \in Proc |-> IF i = root THEN root ELSE NoPrnt]
            /\ rpt = [i \in Proc |-> FALSE]
            /\ msg = {}

    CanSend(i, k) == /\ <<i, k>> \in nbrs
                     /\ prnt[i] # NoPrnt

    Update(i, j) == /\ prnt[i] = NoPrnt
                    /\ <<j, i>> \in msg
                    /\ prnt' = [prnt EXCEPT ![i] = j]
                    /\ UNCHANGED <<rpt, msg>>

    Send(i) == /\ prnt[i] # NoPrnt
               /\ ~rpt[i]
               /\ rpt' = [rpt EXCEPT ![i] = TRUE]
               /\ msg' = msg \cup {<<i, k>> : k \in {s \in Proc : CanSend(i, s)}}
               /\ UNCHANGED prnt

    Next == \E i \in Proc : \/ \E j \in Proc : Update(i, j)
                            \/ Send(i)

    Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

    Safety == \A i \in Proc :
                 (prnt[i] # NoPrnt /\ i # root) => <<prnt[i], i>> \in nbrs
    =========================================================================