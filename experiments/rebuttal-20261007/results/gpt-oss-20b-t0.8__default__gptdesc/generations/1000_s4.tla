------------------------------ MODULE ResourceAllocator ------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS C, R
VARIABLES held, pending
vars == <<held, pending>>

TypeInv ==
  /\ held \in [C -> SUBSET R]
  /\ pending \in [C -> SUBSET R]

AllHeld == \cup (\{held[c] : c \in C\})
FreeResources == R \ AllHeld

IssueReq(c, req) ==
  /\ c \in C
  /\ held[c] = {}
  /\ pending[c] = {}
  /\ req \subseteq R
  /\ pending' = [pending EXCEPT ![c] = req]
  /\ UNCHANGED <<held>>

Allocate(c, res) ==
  /\ c \in C
  /\ res \subseteq pending[c]
  /\ res \subseteq FreeResources
  /\ held'   = [held EXCEPT ![c] = held[c] ∪ res]
  /\ pending'= [pending EXCEPT ![c] = pending[c] \ res]

Release(c, res) ==
  /\ c \in C
  /\ res \subseteq held[c]
  /\ held'   = [held EXCEPT ![c] = held[c] \ res]
  /\ UNCHANGED <<pending>>

Next ==
  \/ \E c \in C, req \subseteq R : IssueReq(c,req)
  \/ \E c \in C, res \subseteq R : Allocate(c,res)
  \/ \E c \in C, res \subseteq R : Release(c,res)

Init ==
  /\ held = [c \in C |-> {}]
  /\ pending = [c \in C |-> {}]

MutualExcl == 
  \A c1,c2 \in C : c1 # c2 => (held[c1] ∩ held[c2]) = {}

EvtReturn ==
  \A c \in C : []<> (held[c] = {})

EvtObtain ==
  \A c \in C : []<>(pending[c] = {})

InfNoUnsatisfied ==
  []<>(\A c \in C : pending[c] = {})

Symmetry == 
  \A f \in [C -> C] :
    /\ (\forall x,y \in C: f[x]=f[y] => x=y)
    /\ (\forall c1,c2 \in C: (held'[c1] = held'[c2]) <=> (pending[c1] = pending[c2]))

SpecWeakFair ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(Allocate)
  /\ []TypeInv
  /\ []MutualExcl

SpecStrongFair ==
  Init
  /\ [][Next]_vars
  /\ SF_vars(Release)
  /\ []TypeInv
  /\ []MutualExcl

Spec == SpecWeakFair

=============================================================================