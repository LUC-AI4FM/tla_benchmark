------------------------- MODULE APAbcastFolklore -----------------------------
(*
 * Typed declarations for the folklore reliable broadcast specification
 * (bcastFolklore). The definitions of bcastFolklore are given inline below
 * so that the module can be parsed and model checked on its own.
 *)
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

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat
ASSUME (N > 2 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }

vars == << pc, rcvd, sent, nCrashed, Corr >>

Init ==
    /\ nCrashed = 0
    /\ Corr = 1 .. N
    /\ sent = {}
    /\ pc \in [ Proc -> {"V0", "V1"} ]
    /\ rcvd = [ i \in Proc |-> {} ]

InitNoBcast ==
    /\ nCrashed = 0
    /\ Corr = 1 .. N
    /\ sent = {}
    /\ pc = [ p \in Proc |-> "V0" ]
    /\ rcvd = [ i \in Proc |-> {} ]

Receive(self) ==
    \E r \in SUBSET (Proc \X M):
        /\ r \subseteq sent
        /\ rcvd[self] \subseteq r
        /\ rcvd' = [rcvd EXCEPT ![self] = r]

UponV1(self) ==
    /\ pc[self] = "V1"
    /\ pc' = [pc EXCEPT ![self] = "AC"]
    /\ sent' = sent \cup { <<self, "ECHO">> }
    /\ nCrashed' = nCrashed
    /\ Corr' = Corr

UponAccept(self) ==
    /\ (pc[self] = "V0" \/ pc[self] = "V1")
    /\ rcvd'[self] # {}
    /\ pc' = [pc EXCEPT ![self] = "AC"]
    /\ sent' = sent \cup { <<self, "ECHO">> }
    /\ nCrashed' = nCrashed
    /\ Corr' = Corr

UponCrash(self) ==
    /\ nCrashed < F
    /\ pc[self] # "CR"
    /\ nCrashed' = nCrashed + 1
    /\ pc' = [pc EXCEPT ![self] = "CR"]
    /\ sent' = sent
    /\ Corr' = Corr \ { self }

Step(self) ==
    /\ Receive(self)
    /\ \/ UponV1(self)
       \/ UponAccept(self)
       \/ UponCrash(self)
       \/ UNCHANGED << pc, sent, nCrashed, Corr >>

Next == \E self \in Corr : Step(self)

Spec == Init /\ [][Next]_vars
          /\ WF_vars(\E self \in Corr :
                        /\ Receive(self)
                        /\ \/ UponV1(self)
                           \/ UponAccept(self)
                           \/ UNCHANGED << pc, sent, nCrashed, Corr >>)

SpecNoBcast == InitNoBcast /\ [][Next]_vars
          /\ WF_vars(\E self \in Corr :
                        /\ Receive(self)
                        /\ \/ UponV1(self)
                           \/ UponAccept(self)
                           \/ UNCHANGED << pc, sent, nCrashed, Corr >>)

TypeOK ==
    /\ sent \subseteq Proc \X M
    /\ pc \in [ Proc -> {"V0", "V1", "AC", "CR"} ]
    /\ rcvd \in [ Proc -> SUBSET sent ]
    /\ nCrashed \in 0 .. N
    /\ Corr \in SUBSET Proc

\* Properties of the folklore broadcast
Unforg ==
    (\A self \in Corr : pc[self] = "V0") => [](\A self \in Corr : pc[self] # "AC")

Corr_Ltl ==
    (\A self \in Corr : pc[self] = "V1") => <>(\E self \in Corr : pc[self] = "AC")

Relay_Ltl ==
    []((\E self \in Corr : pc[self] = "AC") => <>(\A self \in Corr : pc[self] = "AC"))

=============================================================================