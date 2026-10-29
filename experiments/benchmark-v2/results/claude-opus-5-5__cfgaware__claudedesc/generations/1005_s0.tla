------------------------------ MODULE MC_bcastFolklore ------------------------------
(* Folklore reliable broadcast with crash faults, with Apalache type annotations.
   Self-contained: the definitions normally imported from bcastFolklore via
   INSTANCE are inlined here so the module parses on its own. *)

EXTENDS Naturals, FiniteSets

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Int;
    T,
    \* @type: Int;
    F

VARIABLES
    \* @type: Set(Int);
    Corr,
    \* @type: Int;
    nCrashed,
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Set(<<Int, Str>>);
    rcvd,
    \* @type: Set(<<Int, Str>>);
    sent

ASSUME N > 2 * T /\ T >= F /\ F >= 0

Proc == 1 .. N
M == { "ECHO" }

vars == << pc, rcvd, sent, nCrashed, Corr >>

Init ==
    /\ nCrashed = 0
    /\ Corr = Proc
    /\ sent = {}
    /\ pc \in [ Proc -> { "V0", "V1" } ]
    /\ rcvd = [ i \in Proc |-> {} ]

InitNoBcast ==
    /\ nCrashed = 0
    /\ Corr = Proc
    /\ sent = {}
    /\ pc = [ p \in Proc |-> "V0" ]
    /\ rcvd = [ i \in Proc |-> {} ]

Receive(self) ==
    \E r \in SUBSET (Proc \X M):
        /\ r \subseteq sent
        /\ rcvd[self] \subseteq r
        /\ rcvd' = [ rcvd EXCEPT ![self] = r ]

UponV1(self) ==
    /\ pc[self] = "V1"
    /\ pc' = [ pc EXCEPT ![self] = "AC" ]
    /\ sent' = sent \cup { << self, "ECHO" >> }
    /\ nCrashed' = nCrashed
    /\ Corr' = Corr

UponAccept(self) ==
    /\ (pc[self] = "V0" \/ pc[self] = "V1")
    /\ rcvd'[self] # {}
    /\ pc' = [ pc EXCEPT ![self] = "AC" ]
    /\ sent' = sent \cup { << self, "ECHO" >> }
    /\ nCrashed' = nCrashed
    /\ Corr' = Corr

UponCrash(self) ==
    /\ nCrashed < F
    /\ pc[self] # "CR"
    /\ nCrashed' = nCrashed + 1
    /\ pc' = [ pc EXCEPT ![self] = "CR" ]
    /\ sent' = sent
    /\ Corr' = Corr \ { self }

Step(self) ==
    /\ Receive(self)
    /\ \/ UponV1(self)
       \/ UponAccept(self)
       \/ UponCrash(self)
       \/ UNCHANGED << pc, sent, nCrashed, Corr >>

Next ==
    \/ \E self \in Corr : Step(self)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(\E self \in Corr : /\ Receive(self)
                                                          /\ \/ UponV1(self)
                                                             \/ UponAccept(self)
                                                             \/ UNCHANGED << pc, sent, nCrashed, Corr >>)

SpecNoBcast == InitNoBcast /\ [][Next]_vars

TypeOK ==
    /\ sent \in SUBSET (Proc \X M)
    /\ pc \in [ Proc -> { "V0", "V1", "AC", "CR" } ]
    /\ rcvd \in [ Proc -> SUBSET (Proc \X M) ]
    /\ nCrashed \in 0 .. N
    /\ Corr \in SUBSET Proc

Unforg ==
    (\A self \in Corr : pc[self] # "V1") => [](\A self \in Corr : pc[self] # "AC")

CorrLtl ==
    (\A i \in Corr : pc[i] = "V1") => <>(\E i \in Corr : pc[i] = "AC")

RelayLtl ==
    []((\E i \in Corr : pc[i] = "AC") => <>(\A i \in Corr : pc[i] = "AC"))

=============================================================================