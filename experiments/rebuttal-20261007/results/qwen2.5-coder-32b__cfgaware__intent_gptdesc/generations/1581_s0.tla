------------------------------- MODULE DiningPhilosophers -------------------------------
VARIABLES state

CONSTANTS N

ASSUME N \in Nat /\ N >= 2

(*--algorithm dining_philosophers

variables 
    philosophers = {p \in 1..N},
    forks = {f \in 1..N},
    state = [phil \in philosophers |-> "thinking", fork \in forks |-> FALSE];

fair process (phil \in philosophers)
begin
    Think:
        while TRUE do
            await state[phil] = "thinking";
            state[phil] := "hungry";
            pickForks(phil);
            eat(phil);
            putDownForks(phil);
            state[phil] := "thinking";
        end while;
end process;

macro pickForks(p \in philosophers) begin
    with leftFork = (p - 1) % N + 1,
         rightFork = p do
        await \A f \in {leftFork, rightFork}: state[f] = FALSE;
        state[leftFork] := TRUE;
        state[rightFork] := TRUE;
        state[p] := "eating";
    end with;
end macro;

macro eat(p \in philosophers) begin
    skip;  (* eating action *)
end macro;

macro putDownForks(p \in philosophers) begin
    with leftFork = (p - 1) % N + 1,
         rightFork = p do
        state[leftFork] := FALSE;
        state[rightFork] := FALSE;
    end with;
end macro;

end algorithm *)

Invariant == 
    /\ \A f \in forks: Cardinality({p \in philosophers | state[f]}) <= 1
    /\ \A p \in philosophers: state[p] \in {"thinking", "hungry", "eating"}
    /\ \A p \in philosophers: state[p] = "eating" => 
        let leftFork = (p - 1) % N + 1,
            rightFork = p
        in \/ state[leftFork]
           \/ state[rightFork]

StarvationFree ==
    \A p \in philosophers:
        WF_<<p>>_stutter(\E f \in {leftFork, rightFork}: state[f] = FALSE)

Spec == 
    /\ Init
    /\ [][Next]_<<phil>>
    /\ SpecFair

Init == 
    /\ state \in [phil \in philosophers |-> "thinking", fork \in forks |-> FALSE]

Next ==
    \/ \E p \in philosophers: state[p] = "thinking" /\ state' = [state EXCEPT ![p] = "hungry"]
    \/ \E p \in philosophers: pickForksEnabled(p) /\ state' = pickForksAction(state, p)
    \/ \E p \in philosophers: state[p] = "eating" /\ state' = [state EXCEPT ![p] = "thinking", ![leftFork(p)] = FALSE, ![rightFork(p)] = FALSE]

pickForksEnabled(p) ==
    let leftFork = (p - 1) % N + 1,
        rightFork = p
    in state[p] = "hungry" /\ \A f \in {leftFork, rightFork}: state[f] = FALSE

pickForksAction(state, p) ==
    let leftFork = (p - 1) % N + 1,
        rightFork = p
    in [state EXCEPT ![p] = "eating", ![leftFork] = TRUE, ![rightFork] = TRUE]

leftFork(p) == (p - 1) % N + 1

rightFork(p) == p

SpecFair ==
    WF_<<phil>>_stutter(Next)

=============================================================================