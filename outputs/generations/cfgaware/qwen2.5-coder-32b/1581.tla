------------------------------- MODULE DiningPhilosophers -------------------------------
CONSTANTS N

VARIABLES pc, sem

(*--algorithm dining_philosophers
variables 
    pc = [i \in 0..N-1 |-> "think"],
    sem = [f \in 0..N-1 |-> TRUE];

fair process (Philosopher \in 0..N-1) \in 0..N-1
begin
Think:
    await pc[Philosopher] = "think";
    pc[Philosopher] := "try_pickup_right";

TryPickupRight:
    if Philosopher = 0 then
        await sem[(Philosopher - 1) % N];
        sem[(Philosopher - 1) % N] := FALSE;
        pc[Philosopher] := "try_pickup_left";
    else
        await sem[Philosopher];
        sem[Philosopher] := FALSE;
        pc[Philosopher] := "eat";

TryPickupLeft:
    if Philosopher = 0 then
        await sem[Philosopher];
        sem[Philosopher] := FALSE;
        pc[Philosopher] := "eat";
    else
        await sem[(Philosopher - 1) % N];
        sem[(Philosopher - 1) % N] := FALSE;
        pc[Philosopher] := "eat";

Eat:
    await pc[Philosopher] = "eat";
    pc[Philosopher] := "putdown_right";

PutdownRight:
    if Philosopher = 0 then
        sem[Philosopher] := TRUE;
        pc[Philosopher] := "putdown_left";
    else
        sem[(Philosopher - 1) % N] := TRUE;
        pc[Philosopher] := "think";

PutdownLeft:
    if Philosopher = 0 then
        sem[(Philosopher - 1) % N] := TRUE;
        pc[Philosopher] := "think";
end process;

end algorithm;*)

Spec == /\ Init
        /\ [][Next]_<<pc, sem>>
        /\ WF_next

Init == /\ pc \in [0..N-1 -> {"think", "try_pickup_right", "try_pickup_left", "eat", "putdown_right", "putdown_left"}]
        /\ sem \in [0..N-1 -> BOOLEAN]

Next ==
    \/ \E Philosopher \in 0..N-1 : pc[Philosopher] = "think" /\ pc' = [pc EXCEPT ![Philosopher] = "try_pickup_right"]
    \/ \E Philosopher \in 0..N-1 : Philosopher = 0 /\ pc[Philosopher] = "try_pickup_right" /\ sem[(Philosopher - 1) % N] /\ sem' = [sem EXCEPT ![(Philosopher - 1) % N] = FALSE] /\ pc' = [pc EXCEPT ![Philosopher] = "try_pickup_left"]
    \/ \E Philosopher \in 0..N-1 : Philosopher /= 0 /\ pc[Philosopher] = "try_pickup_right" /\ sem[Philosopher] /\ sem' = [sem EXCEPT ![Philosopher] = FALSE] /\ pc' = [pc EXCEPT ![Philosopher] = "eat"]
    \/ \E Philosopher \in 0..N-1 : Philosopher = 0 /\ pc[Philosopher] = "try_pickup_left" /\ sem[Philosopher] /\ sem' = [sem EXCEPT ![Philosopher] = FALSE] /\ pc' = [pc EXCEPT ![Philosopher] = "eat"]
    \/ \E Philosopher \in 0..N-1 : Philosopher /= 0 /\ pc[Philosopher] = "try_pickup_left" /\ sem[(Philosopher - 1) % N] /\ sem' = [sem EXCEPT ![(Philosopher - 1) % N] = FALSE] /\ pc' = [pc EXCEPT ![Philosopher] = "eat"]
    \/ \E Philosopher \in 0..N-1 : pc[Philosopher] = "eat" /\ pc' = [pc EXCEPT ![Philosopher] = "putdown_right"]
    \/ \E Philosopher \in 0..N-1 : Philosopher = 0 /\ pc[Philosopher] = "putdown_right" /\ sem[Philosopher]' = TRUE /\ pc' = [pc EXCEPT ![Philosopher] = "putdown_left"]
    \/ \E Philosopher \in 0..N-1 : Philosopher /= 0 /\ pc[Philosopher] = "putdown_right" /\ sem[(Philosopher - 1) % N]' = TRUE /\ pc' = [pc EXCEPT ![Philosopher] = "think"]
    \/ \E Philosopher \in 0..N-1 : Philosopher = 0 /\ pc[Philosopher] = "putdown_left" /\ sem[(Philosopher - 1) % N]' = TRUE /\ pc' = [pc EXCEPT ![Philosopher] = "think"]

WF_next == WF_vars(Next, <<pc, sem>>)

WF_vars(action, vars) ==
    \A s \in SUBSET (DOMAIN vars) :
        \E r \in [DOMAIN vars -> BOOLEAN] :
            \/ action /\ \A v \in DOMAIN vars : r[v] = (v \notin s)
            \/ ~action /\ \A v \in DOMAIN vars : r[v] = TRUE

Invariant ==
    \A Philosopher \in 0..N-1 :
        ~(\E LeftPhilosopher \in {Philosopher, (Philosopher + 1) % N} :
            pc[LeftPhilosopher] = "eat")

StarvationFree ==
    \A Philosopher \in 0..N-1 :
        [](<>[]pc[Philosopher] = "eat")
=============================================================================