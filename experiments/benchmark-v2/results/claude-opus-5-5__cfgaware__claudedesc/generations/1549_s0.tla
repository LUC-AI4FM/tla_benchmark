------------------------------ MODULE EventuallyPerfectFailureDetector ------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    N,              \* number of processes
    T,              \* maximum number of crash failures
    d0,             \* default (initial) timeout
    SendPoint,      \* a process sends "alive" when localClock % SendPoint = 0
    PredictPoint,   \* a process updates its suspicions when localClock % PredictPoint = 0
    DELTA,          \* bound on message delay (global ticks)
    PHI             \* bound on relative process speed (global ticks without a step)

ASSUME /\ N \in Nat \ {0}
       /\ T \in Nat /\ T < N
       /\ d0 \in Nat
       /\ SendPoint \in Nat \ {0}
       /\ PredictPoint \in Nat \ {0}
       /\ DELTA \in Nat
       /\ PHI \in Nat

Proc == 1..N

Msg == [from : Proc, to : Proc, age : Nat]

VARIABLES
    inTransit,      \* messages travelling in the channel (with age)
    inDelivery,     \* messages ready for delivery (with age)
    suspected,      \* suspected[i] : processes suspected by i
    delta,          \* delta[i][j] : timeout of i for j
    fromLastHeard,  \* fromLastHeard[i][j] : local steps since i last heard from j
    localClock,     \* local clock of each process
    outgoing,       \* messages output by the last step of each process
    procPause,      \* global ticks since process last moved
    moved,          \* moved[i] : i acted since the last global tick
    failed,         \* crash flags
    F               \* number of crashed processes

chanVars == <<inTransit, inDelivery>>
fdVars   == <<suspected, delta, fromLastHeard, localClock, outgoing>>
envVars  == <<procPause, moved, failed, F>>
vars     == <<inTransit, inDelivery, suspected, delta, fromLastHeard,
              localClock, outgoing, procPause, moved, failed, F>>

-----------------------------------------------------------------------------------------------------
(* Age_Channel *)

IncAge(m) == [m EXCEPT !.age = @ + 1]

AgeSet(S) == { IncAge(m) : m \in S }

NewMsgs(i) == { [from |-> i, to |-> k, age |-> 0] : k \in Proc \ {i} }

-----------------------------------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ \A m \in inTransit  : m \in Msg
    /\ \A m \in inDelivery : m \in Msg
    /\ suspected \in [Proc -> SUBSET Proc]
    /\ delta \in [Proc -> [Proc -> Nat]]
    /\ fromLastHeard \in [Proc -> [Proc -> Nat]]
    /\ localClock \in [Proc -> Nat]
    /\ \A i \in Proc : \A m \in outgoing[i] : m \in Msg
    /\ DOMAIN outgoing = Proc
    /\ procPause \in [Proc -> Nat]
    /\ moved \in [Proc -> BOOLEAN]
    /\ failed \in [Proc -> BOOLEAN]
    /\ F \in 0..T

-----------------------------------------------------------------------------------------------------
Init ==
    /\ inTransit = {}
    /\ inDelivery = {}
    /\ suspected = [i \in Proc |-> {}]
    /\ delta = [i \in Proc |-> [j \in Proc |-> d0]]
    /\ fromLastHeard = [i \in Proc |-> [j \in Proc |-> 0]]
    /\ localClock = [i \in Proc |-> 0]
    /\ outgoing = [i \in Proc |-> {}]
    /\ procPause = [i \in Proc |-> 0]
    /\ moved = [i \in Proc |-> FALSE]
    /\ failed = [i \in Proc |-> FALSE]
    /\ F = 0

-----------------------------------------------------------------------------------------------------
(* EPFailureDetector : behavior of a correct process *)

IncHeard(i) == [k \in Proc |-> IF k = i THEN 0 ELSE fromLastHeard[i][k] + 1]

IsSendStep(i)    == localClock[i] % SendPoint = 0
IsPredictStep(i) == ~IsSendStep(i) /\ localClock[i] % PredictPoint = 0
IsReceiveStep(i) == ~IsSendStep(i) /\ ~IsPredictStep(i)

Send(i) ==
    /\ IsSendStep(i)
    /\ inTransit' = inTransit \cup NewMsgs(i)
    /\ outgoing' = [outgoing EXCEPT ![i] = NewMsgs(i)]
    /\ fromLastHeard' = [fromLastHeard EXCEPT ![i] = IncHeard(i)]
    /\ UNCHANGED <<inDelivery, suspected, delta>>

Predict(i) ==
    /\ IsPredictStep(i)
    /\ LET flh == IncHeard(i) IN
         /\ fromLastHeard' = [fromLastHeard EXCEPT ![i] = flh]
         /\ suspected' = [suspected EXCEPT ![i] =
                @ \cup { k \in Proc \ {i} : flh[k] > delta[i][k] }]
    /\ outgoing' = [outgoing EXCEPT ![i] = {}]
    /\ UNCHANGED <<inTransit, inDelivery, delta>>

Receive(i) ==
    /\ IsReceiveStep(i)
    /\ outgoing' = [outgoing EXCEPT ![i] = {}]
    /\ \/ \E m \in inDelivery :
            /\ m.to = i
            /\ inDelivery' = inDelivery \ {m}
            /\ fromLastHeard' = [fromLastHeard EXCEPT ![i] =
                    [k \in Proc |-> IF k = i \/ k = m.from THEN 0
                                    ELSE fromLastHeard[i][k] + 1]]
            /\ IF m.from \in suspected[i]
                 THEN /\ suspected' = [suspected EXCEPT ![i] = @ \ {m.from}]
                      /\ delta' = [delta EXCEPT ![i][m.from] = @ + 1]
                 ELSE UNCHANGED <<suspected, delta>>
       \/ /\ ~\E m \in inDelivery : m.to = i
          /\ fromLastHeard' = [fromLastHeard EXCEPT ![i] = IncHeard(i)]
          /\ UNCHANGED <<inDelivery, suspected, delta>>
    /\ UNCHANGED inTransit

ProcStep(i) ==
    /\ (Send(i) \/ Predict(i) \/ Receive(i))
    /\ localClock' = [localClock EXCEPT ![i] = @ + 1]
    /\ moved' = [moved EXCEPT ![i] = TRUE]
    /\ procPause' = [procPause EXCEPT ![i] = 0]
    /\ UNCHANGED <<failed, F>>

(* Drain a message addressed to an already crashed process *)
DrainCrashed ==
    \E i \in Proc :
        /\ failed[i]
        /\ \/ \E m \in inTransit :
                 /\ m.to = i
                 /\ inTransit' = inTransit \ {m}
                 /\ UNCHANGED inDelivery
           \/ \E m \in inDelivery :
                 /\ m.to = i
                 /\ inDelivery' = inDelivery \ {m}
                 /\ UNCHANGED inTransit
        /\ UNCHANGED <<fdVars, envVars>>

-----------------------------------------------------------------------------------------------------
(* Environment *)

Crash ==
    \E i \in Proc :
        /\ ~failed[i]
        /\ F < T
        /\ failed' = [failed EXCEPT ![i] = TRUE]
        /\ F' = F + 1
        /\ UNCHANGED <<chanVars, fdVars, procPause, moved>>

EnvTick ==
    /\ \E i \in Proc : ~failed[i] /\ moved[i]
    /\ \E D \in SUBSET inTransit :
         /\ inTransit' = AgeSet(inTransit \ D)
         /\ inDelivery' = AgeSet(inDelivery \cup D)
    /\ procPause' = [i \in Proc |-> IF failed[i] THEN procPause[i]
                                    ELSE procPause[i] + 1]
    /\ moved' = [i \in Proc |-> FALSE]
    /\ UNCHANGED <<fdVars, failed, F>>

ProcTick ==
    \/ \E i \in Proc : ~failed[i] /\ ~moved[i] /\ ProcStep(i)
    \/ DrainCrashed

-----------------------------------------------------------------------------------------------------
(* Partial synchrony constraints (state predicates, applied to next states) *)

DELTAConstraint == \A m \in inTransit : m.age <= DELTA

PHIConstraint == \A i \in Proc : ~failed[i] => procPause[i] <= PHI

Next ==
    /\ (Crash \/ EnvTick \/ ProcTick)
    /\ DELTAConstraint'
    /\ PHIConstraint'

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(EnvTick /\ DELTAConstraint' /\ PHIConstraint')
    /\ WF_vars(ProcTick /\ DELTAConstraint' /\ PHIConstraint')

-----------------------------------------------------------------------------------------------------
(* Properties *)

StrongCompleteness ==
    <>[](\A i, j \in Proc :
            (failed[i] /\ ~failed[j]) => i \in suspected[j])

EventuallyStrongAccuracy ==
    <>[](\A i, j \in Proc :
            (~failed[i] /\ ~failed[j]) => i \notin suspected[j])

NeverPermanentlySuspected ==
    \A i, j \in Proc :
        [](( ~failed[i] /\ ~failed[j] /\ i \in suspected[j])
              => <>(failed[i] \/ failed[j] \/ i \notin suspected[j]))

StateConstraint == TLCGet("level") <= 20

=====================================================================================================