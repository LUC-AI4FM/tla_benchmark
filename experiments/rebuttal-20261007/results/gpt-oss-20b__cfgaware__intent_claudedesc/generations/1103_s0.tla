MODULE NBAC

CONSTANT N

VARIABLES initVote, sent, recv, dec, crashed, fd

(***************************************************************************)
(*  Type safety predicate                                                     *)
(***************************************************************************)

TypeOK == 
    /\ N \in Nat
    /\ N > 0
    /\ initVote \in [1..N -> {"YES","NO"}]
    /\ sent \subseteq { [sender |