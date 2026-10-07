------------------------------ MODULE ResourceAllocator ------------------------------

EXTENDS Naturals

CONSTANTS Client, Resource

ASSUME Client = {c1, c2, c3} /\ Resource = {r1, r2}

VARIABLES unsat, alloc

vars == << unsat, alloc >>

TypeInvariant ==
  /\ unsat \in [Client -> SUBSET Resource]
  /\ alloc \in [Client -> SUBSET Resource]
  /\ \A c \in Client : alloc[c] \cap unsat[c] = {}

ResourceMutex ==
  \A c, d \in Client :
    c = d \/ (alloc[c] \cap alloc[d] = {})

Init ==
  /\ unsat = [c \in Client |-> {}]
  /\ alloc = [c \in Client |-> {}]

Available ==
  Resource \ UNION { alloc[c] : c \in Client }

Request(c, S) ==
  /\ c \in Client
  /\ S \subseteq Resource /\ S /= {}
  /\ alloc[c] = {} /\ unsat[c] = {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

Allocate(c, S) ==
  /\ c \in Client
  /\ S \subseteq (Available \cap unsat[c])
  /\ S /= {}
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

Return(c, S) ==
  /\ c \in Client
  /\ S \subseteq alloc[c]
  /\ S /= {}
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \cup S]

FullReturn(c) ==
  /\ c \in Client
  /\ alloc[c] /= {}
  /\ alloc' = [alloc EXCEPT ![c] = {}]
  /\ unsat' = [unsat EXCEPT ![c] = @ \cup alloc[c]]

FullReturnWhenSatisfied(c) ==
  /\ unsat[c] = {}
  /\ FullReturn(c)

Next ==
  \E c \in Client :
    \E S \in SUBSET Resource :
      Request(c, S) \/ Allocate(c, S) \/ Return(c, S)

NonEmptySubsets(S) == { T \in SUBSET S : T /= {} }

FairAlloc ==
  \A c \in Client :
    \A S \in NonEmptySubsets(Resource) :
      SF_vars(Allocate(c, S))

FairFullReturn ==
  \A c \in Client : WF_vars(FullReturn(c))

FairFullReturn2 ==
  \A c \in Client : WF_vars(FullReturnWhenSatisfied(c))

SimpleAllocator ==
  Init /\ [][Next]_vars /\ FairAlloc /\ FairFullReturn

SimpleAllocator2 ==
  Init /\ [][Next]_vars /\ FairAlloc /\ FairFullReturn2

Spec == SimpleAllocator
Spec2 == SimpleAllocator2

ClientsWillReturn ==
  \A c \in Client : [](unsat[c] = {} => <> (alloc[c] = {}))

ClientsWillObtain ==
  \A c \in Client :
    \A r \in Resource :
      [] (r \in unsat[c] => <> (r \in alloc[c]))

InfOftenSatisfied ==
  \A c \in Client : []<>(unsat[c] = {})

THEOREM Spec => []TypeInvariant /\ []ResourceMutex

THEOREM Spec => ClientsWillReturn /\ ClientsWillObtain /\ InfOftenSatisfied

THEOREM Spec2 => []TypeInvariant /\ []ResourceMutex

THEOREM Spec2 => ClientsWillReturn

=============================================================================