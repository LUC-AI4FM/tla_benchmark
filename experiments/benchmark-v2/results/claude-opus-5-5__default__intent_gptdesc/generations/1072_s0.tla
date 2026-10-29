---------------------------- MODULE RingTerminationDetection ----------------------------
(***************************************************************************)
(* Termination detection on a fixed directed ring of processes.            *)
(* It uses a circulating token in the style of Safra / EWD998, together    *)
(* with point-to-point payload messages and vector clocks.                 *)
(*                                                                         *)
(* Processes are 0..N-1. The ring is the directed cycle p -> (p+1) % N.    *)
(* Process 0 is the distinguished initiator of probe rounds.               *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Procs     == 0 .. (N - 1)
Initiator == 0
Succ(p)   == (p + 1) % N

Colors    == {"white", "black"}

VClock    == [Procs -> Nat]
ZeroVC    == [i \in Procs |-> 0]
Merge(a, b) == [i \in Procs |-> IF a[i] >= b[i] THEN a[i] ELSE b[i]]
Tick(v, p)  == [v EXCEPT ![p] = @ + 1]
VCLeq(a, b) == \A i \in Procs : a[i] <= b[i]

Msg   == [src : Procs, vc : VClock]
Token == [pos : Procs, q : Int, color : Colors, vc : VClock, started : BOOLEAN]

VARIABLES
    active,          \* active[p] : process p is performing local work
    color,           \* color[p]  : local color of p (white/black)
    counter,         \* counter[p]: payloads sent minus payloads received by p
    vc,              \* vc[p]     : vector clock of p
    inbox,           \* inbox[p]  : in-flight payload messages addressed to p
    token,           \* the circulating token with its probe metadata
    detected,        \* the initiator has announced termination
    quiescentRounds  \* auxiliary: token circulations completed since quiescence

vars == <<active, color, counter, vc, inbox, token, detected, quiescentRounds>>

-----------------------------------------------------------------------------
(* Auxiliary operators *)

RECURSIVE SumF(_, _)
SumF(f, S) == IF S = {} THEN 0
              ELSE LET x == CHOOSE x \in S : TRUE
                   IN  f[x] + SumF(f, S \ {x})

InFlight == SumF([p \in Procs |-> Len(inbox[p])], Procs)

Terminated == /\ \A p \in Procs : ~active[p]
              /\ InFlight = 0

RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

(* Processes that have already forwarded the token in the current round. *)
Visited ==
    IF token.pos = Initiator
    THEN IF token.started THEN Procs \ {Initiator} ELSE {}
    ELSE 1 .. (token.pos - 1)

Unvisited == Procs \ Visited

(* The initiator's termination-detection condition. *)
DetectCond ==
    /\ token.pos = Initiator
    /\ token.started
    /\ token.color = "white"
    /\ color[Initiator] = "white"
    /\ ~active[Initiator]
    /\ token.q + counter[Initiator] = 0

-----------------------------------------------------------------------------
TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ color \in [Procs -> Colors]
    /\ counter \in [Procs -> Int]
    /\ vc \in [Procs -> VClock]
    /\ inbox \in [Procs -> Seq(Msg)]
    /\ token \in Token
    /\ detected \in BOOLEAN
    /\ quiescentRounds \in Nat

Init ==
    /\ active \in [Procs -> BOOLEAN]
    /\ color = [p \in Procs |-> "white"]
    /\ counter = [p \in Procs |-> 0]
    /\ vc = [p \in Procs |-> ZeroVC]
    /\ inbox = [p \in Procs |-> <<>>]
    /\ token = [pos |-> Initiator, q |-> 0, color |-> "black",
                vc |-> ZeroVC, started |-> FALSE]
    /\ detected = FALSE
    /\ quiescentRounds = 0

-----------------------------------------------------------------------------
(* Payload send: an active process sends a payload stamped with its clock. *)
SendMsg(p, r) ==
    /\ active[p]
    /\ LET vp == Tick(vc[p], p)
       IN  /\ vc' = [vc EXCEPT ![p] = vp]
           /\ inbox' = [inbox EXCEPT ![r] = Append(@, [src |-> p, vc |-> vp])]
    /\ counter' = [counter EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<active, color, token, detected, quiescentRounds>>

(* Payload receive: merge the stamp, reactivate, blacken, decrement counter. *)
RecvMsg(p) ==
    \E i \in 1 .. Len(inbox[p]) :
        LET m == inbox[p][i]
        IN  /\ inbox' = [inbox EXCEPT ![p] = RemoveAt(@, i)]
            /\ vc' = [vc EXCEPT ![p] = Tick(Merge(@, m.vc), p)]
            /\ active' = [active EXCEPT ![p] = TRUE]
            /\ color' = [color EXCEPT ![p] = "black"]
            /\ counter' = [counter EXCEPT ![p] = @ - 1]
            /\ UNCHANGED <<token, detected, quiescentRounds>>

(* Local deactivation. *)
Deactivate(p) ==
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<color, counter, vc, inbox, token, detected, quiescentRounds>>

(* Token pass by a non-initiator. It accumulates the counter and color,  *)
(* and merges vector clocks into both the token and the receiver.        *)
PassToken(p) ==
    /\ token.pos = p
    /\ p # Initiator
    /\ ~active[p]
    /\ LET s   == Succ(p)
           vp  == Tick(vc[p], p)
           tvc == Merge(token.vc, vp)
       IN  /\ token' = [token EXCEPT !.pos   = s,
                                     !.q     = @ + counter[p],
                                     !.color = IF color[p] = "black"
                                               THEN "black" ELSE @,
                                     !.vc    = tvc]
           /\ vc' = [vc EXCEPT ![p] = vp,
                               ![s] = Tick(Merge(vc[s], tvc), s)]
           /\ quiescentRounds' = IF s = Initiator /\ Terminated
                                 THEN quiescentRounds + 1
                                 ELSE quiescentRounds
    /\ color' = [color EXCEPT ![p] = "white"]
    /\ UNCHANGED <<active, counter, inbox, detected>>

(* The initiator starts a new probe round. *)
StartRound ==
    LET s  == Succ(Initiator)
        v0 == Tick(vc[Initiator], Initiator)
    IN  /\ token' = [pos |-> s, q |-> 0, color |-> "white",
                     vc |-> v0, started |-> TRUE]
        /\ vc' = IF s = Initiator
                 THEN [vc EXCEPT ![Initiator] = v0]
                 ELSE [vc EXCEPT ![Initiator] = v0,
                                 ![s] = Tick(Merge(vc[s], v0), s)]
        /\ color' = [color EXCEPT ![Initiator] = "white"]
        /\ quiescentRounds' = IF s = Initiator /\ Terminated
                              THEN quiescentRounds + 1
                              ELSE quiescentRounds
        /\ UNCHANGED <<active, counter, inbox, detected>>

(* The initiator holds the token. It either detects termination or      *)
(* starts a new round.                                                  *)
InitiatorStep ==
    /\ token.pos = Initiator
    /\ ~active[Initiator]
    /\ ~detected
    /\ IF DetectCond
       THEN /\ detected' = TRUE
            /\ UNCHANGED <<active, color, counter, vc, inbox, token, quiescentRounds>>
       ELSE StartRound

TokenPass == \E p \in Procs : PassToken(p)

Next ==
    \/ \E p, r \in Procs : SendMsg(p, r)
    \/ \E p \in Procs : RecvMsg(p)
    \/ \E p \in Procs : Deactivate(p)
    \/ TokenPass
    \/ InitiatorStep

Fairness ==
    /\ WF_vars(TokenPass)
    /\ WF_vars(InitiatorStep)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

(* Soundness: detection implies global termination. *)
Soundness == detected => Terminated

(* The detection condition itself implies global termination. *)
DetectionImpliesTermination == DetectCond => Terminated

(* Counter invariant: the counters sum to the number of in-flight payloads. *)
CounterInv == SumF(counter, Procs) = InFlight

(* Token-metadata invariant (Safra / EWD998). *)
SafraInv ==
    \/ /\ \A i \in Visited : ~active[i]
       /\ token.q = SumF(counter, Visited)
    \/ SumF(counter, Unvisited) + token.q > 0
    \/ \E i \in Unvisited : color[i] = "black"
    \/ token.color = "black"

(* A pending payload that could reactivate work blocks detection. *)
PendingBlocksDetection == (InFlight > 0) => ~DetectCond

(* Vector-clock causal merging semantics. *)
VCInv ==
    \* Only p advances its own component.
    /\ \A p, r \in Procs : vc[r][p] <= vc[p][p]
    \* Message stamps are causally dominated by the sender's clock.
    /\ \A p \in Procs : \A i \in 1 .. Len(inbox[p]) :
          /\ VCLeq(inbox[p][i].vc, vc[inbox[p][i].src])
          /\ inbox[p][i].vc[inbox[p][i].src] >= 1
    \* The token's stamp has been merged into the holder's clock.
    /\ VCLeq(token.vc, vc[token.pos])

(* Bounded detection: at most three full circulations after quiescence. *)
BoundedDetection ==
    /\ quiescentRounds <= 3
    /\ (quiescentRounds = 3) => (detected \/ DetectCond)

Invariants ==
    /\ TypeOK
    /\ Soundness
    /\ DetectionImpliesTermination
    /\ CounterInv
    /\ SafraInv
    /\ PendingBlocksDetection
    /\ VCInv
    /\ BoundedDetection

(* Termination is stable. *)
TerminationStable == [][Terminated => Terminated']_vars

-----------------------------------------------------------------------------
(* Liveness *)

(* Once quiescent, the initiator eventually detects termination. *)
EventualDetection == Terminated ~> detected

(* Detection occurs within three token circulations after quiescence. *)
BoundedEventualDetection ==
    Terminated ~> (detected /\ quiescentRounds <= 3)

THEOREM Spec => []Invariants
THEOREM Spec => TerminationStable
THEOREM Spec => EventualDetection
THEOREM Spec => BoundedEventualDetection
=============================================================================