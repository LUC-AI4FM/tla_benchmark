MODULE ResourceAllocator
EXTENDS Sequences

CONSTANTS Clients, Resources

VARIABLES owned, req

(* ------------------------------------------------------------------ *)
(* Type invariants *)

typeInvariant == 
  /\ owned \in [Clients -> SUBSET Resources]
  /\ req   \in [Clients -> SUBSET Resources]

ownedReqInvariant ==
  \A c \in Clients : owned[c] \subseteq req[c]

(* ------------------------------------------------------------------ *)
(* Mutual exclusion of resource ownership *)

Count(S) == Len(SeqFromSet(S))

mutualExcl ==
  \A r \in Resources :
    Count({c \in Clients : r \in owned[c]}) <= 1

(* ------------------------------------------------------------------ *)
(* Operations *)

canRequest(c, R) ==
  /\ c \in Clients
  /\ R \subseteq Resources
  /\ owned[c] = {} 
  /\ req[c]   = {}

requestAction ==
  \E c,R \in Resources :
    /\ canRequest(c, R)
    /\ UNCHANGED <<owned>>
    /\ req' = [req EXCEPT ![c] = R]

allocateAction ==
  \E c,r \in Resources :
    /\ c \in Clients
    /\ r \in req[c]
    /\ r \notin \Union(owned)
    /\ UNCHANGED <<req>>
    /\ owned' = [owned EXCEPT ![c] = owned[c] \cup {r}]

returnAction ==
  \E c,S \subseteq Resources :
    /\ c \in Clients
    /\ S \subseteq owned[c]
    /\ UNCHANGED <<req>>
    /\ owned' = [owned EXCEPT ![c] = owned[c] \ S]

Next == requestAction \/ allocateAction \/ returnAction

Init ==
  /\ typeInvariant
  /\ \A c \in Clients : owned[c] = {} /\ req[c] = {}

(* ------------------------------------------------------------------ *)
(* Two specifications with different fairness assumptions *)

SpecWeakFair == Init /\ [] Next /\ WF_2(allocateAction)

SpecStrongFair == Init /\ [] Next /\ SF_2(requestAction \/ allocateAction \/ returnAction)

(* ------------------------------------------------------------------ *)
(* Safety invariants *)

TypeCorrectness       == typeInvariant
MutualExclusionInv    == mutualExcl

(* ------------------------------------------------------------------ *)
(* Liveness properties *)

EventualReturn ==
  \A c \in Clients :
    [](owned[c] /= {}) => <> (owned[c] = {})

EventualObtainment ==
  \A c \in Clients :
    []((req[c] /= {} /\ owned[c] = {})) => <> (owned[c] = req[c])

InfNoUnsatisfiedRequests ==
  []( <> (\A c \in Clients : req[c] = {}))

(* ------------------------------------------------------------------ *)
(* Symmetry expression *)

Symmetry == 
  \A perm \in [Clients -> Clients] :
    (perm \in {f | f \in [Clients -> Clients]} ) =>
      (\E o', r' :
        <<o', r'>> = [c \in Clients |-> [owned[perm(c)], req[perm(c)]]])

(* ------------------------------------------------------------------ *)
(* Counterexample value structure *)

CounterExample ==
  LET
    C == {"C1", "C2"}
    R == {"R1", "R2"}
  IN
    [Clients -> C, Resources -> R]

(* ------------------------------------------------------------------ *)
(* Theorems (for illustration) *)

THEOREM SpecWeakFair => TypeCorrectness
THEOREM SpecWeakFair => MutualExclusionInv
THEOREM SpecStrongFair => EventualReturn
THEOREM SpecStrongFair => EventualObtainment

END MODULE