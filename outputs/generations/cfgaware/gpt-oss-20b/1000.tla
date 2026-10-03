------------------------------ MODULE ResourceAllocator ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Clients, Resources

VARIABLES owned, pending

(* --------------------------------------------------------------------------- *)
(* Type correctness *)
TypeOK == /\ owned \in [Clients -> SUBSET Resources]
          /\ pending \in [Clients -> BOOLEAN]

(* --------------------------------------------------------------------------- *)
(* Mutual exclusion of resource ownership *)
MutualExclusion ==
  \A r \in Resources:
    #({c \in Clients : r \in owned[c]}) <= 1

(* --------------------------------------------------------------------------- *)
(* A client may issue a request only when it holds no resources and has no
   outstanding unsatisfied request. *)
RequestAllowed(c) == /\ owned[c] = {} 
                     /\ ~pending[c]

(* --------------------------------------------------------------------------- *)
(* Request action: client c requests a set of resources (may be partially granted later). *)
Request(c, reqSet) ==
  /\ RequestAllowed(c)
  /\ pending' = [pending EXCEPT ![c] = TRUE]
  /\ UNCHANGED <<owned>>

(* --------------------------------------------------------------------------- *)
(* Grant action: grant a subset of requested resources to client c. *)
Grant(c, grantSet) ==
  /\ pending[c]
  /\ grantSet \subseteq Resources
  /\ owned' = [owned EXCEPT ![c] = owned[c] \cup grantSet]
  /\ UNCHANGED <<pending>>

(* --------------------------------------------------------------------------- *)
(* Return action: client returns some or all held resources. *)
Return(c, retSet) ==
  LET newOwned == [owned EXCEPT ![c] = owned[c] \setminus retSet] IN
      /\ owned' = newOwned
      /\ pending' =
          IF #newOwned[c] = 0 THEN [pending EXCEPT ![c] = FALSE]
          ELSE pending

(* --------------------------------------------------------------------------- *)
(* Next-state relation *)
Next ==
  \/ \E c \in Clients, reqSet \subseteq Resources:
        Request(c, reqSet)
  \/ \E c \in Clients, grantSet \subseteq Resources:
        Grant(c, grantSet)
  \/ \E c \in Clients, retSet \subseteq owned[c]:
        Return(c, retSet)

(* --------------------------------------------------------------------------- *)
(* Initial state *)
Init == /\ owned = [c \in Clients |-> {}]
          /\ pending = [c \in Clients |-> FALSE]

(* --------------------------------------------------------------------------- *)
(* Two temporal specifications with different fairness assumptions *)
Spec1 == Init /\ [] Next
Spec2 == Init /\ WF_vars(Next)

(* --------------------------------------------------------------------------- *)
(* Liveness properties *)
EventualReturn ==
  [] (pending => <> ~pending)

EventualObtainment ==
  [] (~pending => <> pending)

InfNoUnsatisfied ==
  [] <> ~(\E c \in Clients : pending[c])

(* --------------------------------------------------------------------------- *)
(* Symmetry expression *)
Symmetry == 
  \A c1, c2 \in Clients :
    (\E r \in Resources : r \in owned[c1] <=> r \in owned[c2]) 

(* --------------------------------------------------------------------------- *)
(* Concrete counterexample value structure *)
Counterexample == [c \in Clients |-> {}]

=============================================================================