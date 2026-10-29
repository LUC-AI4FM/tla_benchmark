------------------------------ MODULE EventuallyPerfectFD ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N,             \* number of processes
          T,             \* maximum number of crashes
          d0,            \* initial timeout interval
          SendPoint,     \* local-clock period for broadcasting "alive"
          PredictPoint,  \* local-clock period for updating suspicions
          DELTA,         \* message-delay bound
          PHI            \* relative-speed bound

ASSUME /\ N \in Nat \ {0}
       /\ T \in Nat /\ T < N
       /\ d0 \in Nat
       /\ SendPoint \in Nat \ {0, 1}
       /\ PredictPoint \in Nat \ {0, 1}
       /\ DELTA \in Nat \ {0}
       /\ PHI \in Nat \ {0}

VARIABLES alive,      \* set of correct (non-crashed) processes
          msgs,       \* in-transit messages: records [from, to, age]
          clock,      \* local clocks (modular)
          delta,      \* per-peer timeout intervals
          suspected,  \* suspicion sets
          flh,        \* time (local steps) since last heard from each peer
          pause       \* global ticks since each process last acted

vars == <<alive, msgs, clock, delta, suspected, flh, pause>>

Proc == 1..N

Min(a, b) == IF a <= b THEN a ELSE b

MaxClock == SendPoint * PredictPoint

Msg == [from : Proc, to : Proc, age : 0..DELTA]

Op(p) == IF clock[p] % SendPoint = 0 THEN "send"
         ELSE IF clock[p] % PredictPoint = 0 THEN "predict"
         ELSE "receive"

TypeOK ==
  /\ alive \subseteq Proc
  /\ msgs \subseteq Msg
  /\ clock \in [Proc -> 0..(MaxClock - 1)]
  /\ delta \in [Proc -> [Proc -> Nat]]
  /\ suspected \in [Proc -> SUBSET Proc]
  /\ flh \in [Proc -> [Proc -> Nat]]
  /\ pause \in [Proc -> 0..PHI]

Init ==
  /\ alive = Proc
  /\ msgs = {}
  /\ clock = [p \in Proc |-> 0]
  /\ delta = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ suspected = [p \in Proc |-> {}]
  /\ flh = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ pause = [p \in Proc |-> 0]

\* One global (environmental) tick: a nonempty set of correct processes acts,
\* including every process that would otherwise violate the PHI bound.
Tick ==
  \E A \in SUBSET alive :
    /\ A # {}
    /\ {p \in alive : pause[p] >= PHI - 1} \subseteq A
    /\ LET Senders    == {p \in A : Op(p) = "send"}
           Predictors == {p \in A : Op(p) = "predict"}
           Receivers  == {p \in A : Op(p) = "receive"}
           Receivable == {m \in msgs : m.to \in Receivers}
           Overdue    == {m \in Receivable : m.age >= DELTA}
       IN \E D \in SUBSET Receivable :
            /\ Overdue \subseteq D
            /\ LET Heard(p) == {m.from : m \in {x \in D : x.to = p}}
                   NewMsgs  == {[from |-> p, to |-> q, age |-> 0] :
                                  p \in Senders, q \in alive \ {p}}
                   Remaining == msgs \ D
               IN
               /\ msgs' = {[m EXCEPT !.age = Min(m.age + 1, DELTA)] : m \in Remaining}
                            \cup NewMsgs
               /\ clock' = [p \in Proc |->
                              IF p \in A THEN (clock[p] + 1) % MaxClock ELSE clock[p]]
               /\ pause' = [p \in Proc |->
                              IF p \in A THEN 0
                              ELSE IF p \in alive THEN Min(pause[p] + 1, PHI)
                              ELSE 0]
               /\ flh' = [p \in Proc |-> [q \in Proc |->
                              IF p \in A
                                THEN IF p \in Receivers /\ q \in Heard(p)
                                       THEN 0
                                       ELSE Min(flh[p][q] + 1, delta[p][q] + 1)
                                ELSE flh[p][q]]]
               /\ delta' = [p \in Proc |-> [q \in Proc |->
                              IF p \in Receivers /\ q \in Heard(p) /\ q \in suspected[p]
                                THEN delta[p][q] + 1
                                ELSE delta[p][q]]]
               /\ suspected' = [p \in Proc |->
                              IF p \in Predictors
                                THEN suspected[p] \cup
                                       {q \in Proc \ {p} : flh[p][q] > delta[p][q]}
                              ELSE IF p \in Receivers
                                THEN suspected[p] \ Heard(p)
                              ELSE suspected[p]]
    /\ UNCHANGED alive

Crash ==
  /\ Cardinality(Proc \ alive) < T
  /\ \E p \in alive :
       /\ alive' = alive \ {p}
       /\ pause' = [pause EXCEPT ![p] = 0]
  /\ UNCHANGED <<msgs, clock, delta, suspected, flh>>

Flush ==
  /\ \E m \in msgs :
       /\ m.to \notin alive
       /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<alive, clock, delta, suspected, flh, pause>>

Next == Tick \/ Crash \/ Flush

Spec == Init /\ [][Next]_vars /\ WF_vars(Tick) /\ WF_vars(Flush)

-----------------------------------------------------------------------------

StrongCompleteness ==
  <>[](\A p \in alive : \A q \in Proc \ alive : q \in suspected[p])

EventuallyStrongAccuracy ==
  <>[](\A p \in alive : \A q \in alive : q \notin suspected[p])

NeverPermanentlySuspected ==
  \A p, q \in Proc :
    []<>(~(p \in alive /\ q \in alive /\ q \in suspected[p]))

StateConstraint ==
  \A p, q \in Proc :
    delta[p][q] <= d0 + DELTA + PHI * (SendPoint + PredictPoint)

=============================================================================