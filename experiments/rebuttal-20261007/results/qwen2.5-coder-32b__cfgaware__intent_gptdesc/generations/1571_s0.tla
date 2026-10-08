------------------------------- MODULE DiningPhilosophers -------------------------------
CONSTANTS N

VARIABLES forks, philosophers

(*--algorithm dining_philosophers

variables 
    forks = [i \in 1..N -> FALSE],  (* Forks are initially free *)
    philosophers = [p \in 1..N -> "thinking"]  (* Philosophers start thinking *)

process Philosopher \in 1..N
begin
    while TRUE do
        await (forks[self] \/ forks[(self % N) + 1]) = FALSE;
        atomic {
            if forks[self] = FALSE then forks[self]' := TRUE; end if;
            if forks[(self % N) + 1] = FALSE then forks[(self % N) + 1]' := TRUE; end if;
        };
        philosophers[self]' := "eating";
        skip;  (* Eating *)
        atomic {
            forks[self]' := FALSE;
            forks[(self % N) + 1]' := FALSE;
        };
        philosophers[self]' := "thinking";
    end while
end process

end algorithm*)

Spec == 
    /\ Init
    /\ [][Next]_<<philosophers, forks>>
    /\ WF_next(<<philosophers, forks>>)

Init ==
    /\ forks = [i \in 1..N -> FALSE]
    /\ philosophers = [p \in 1..N -> "thinking"]

Next ==
    \/ \E p \in 1..N : PhilosopherAction(p)
    
PhilosopherAction(p) ==
    LET leftFork == p
        rightFork == (p % N) + 1
    IN
        /\ philosophers' = [philosophers EXCEPT ![p] = CASE 
            philosophers[p] = "thinking" /\ forks[leftFork] = FALSE /\ forks[rightFork] = FALSE -> "eating"
            philosophers[p] = "eating" -> "thinking"
            ELSE philosophers[p]]
        /\ forks' = [forks EXCEPT
            IF philosophers[p] = "thinking" /\ forks[leftFork] = FALSE /\ forks[rightFork] = FALSE THEN
                ![leftFork] = TRUE,
                ![rightFork] = TRUE
            ELSE IF philosophers[p] = "eating" THEN
                ![leftFork] = FALSE,
                ![rightFork] = FALSE
            ENDIF]

WF_next(vars) == 
    WF_vars(Next)

Invariant ==
    /\ \A p \in 1..N : philosophers[p] \in {"thinking", "eating"}
    /\ \A f \in 1..N : forks[f] \in {TRUE, FALSE}
    /\ \A p \in 1..N : 
        (philosophers[p] = "eating" => forks[p] = TRUE /\ forks[(p % N) + 1] = TRUE)
    /\ \A f \in 1..N : 
        Cardinality({p \in 1..N : forks[f] = TRUE}) <= 1

=============================================================================