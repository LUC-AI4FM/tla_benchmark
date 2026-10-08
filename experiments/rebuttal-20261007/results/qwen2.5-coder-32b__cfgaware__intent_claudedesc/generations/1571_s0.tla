------------------------------- MODULE DiningPhilosophers -------------------------------
CONSTANTS N

VARIABLES forks, philosophers

(*--algorithm DiningPhilosophers
variables 
    forks = [i \in 0..N-1 |-> TRUE],  (* TRUE means fork is available *)
    philosophers = [p \in 0..N-1 |-> "thinking"]  (* "thinking" or "eating" *)

process Philosopher \in 0..N-1
begin
    while TRUE do
        if p = 0 then
            /\ await(forks[p])
            /\ forks' = [forks EXCEPT ![p] = FALSE]
            /\ await(forks[(p+1) % N])
            /\ forks' = [forks' EXCEPT ![ (p+1) % N ] = FALSE]
        else
            /\ await(forks[(p+1) % N])
            /\ forks' = [forks EXCEPT ![ (p+1) % N ] = FALSE]
            /\ await(forks[p])
            /\ forks' = [forks' EXCEPT ![p] = FALSE]
        end if;
        
        /\ philosophers' = [philosophers EXCEPT ![p] = "eating"]
        /\ skip;  (* eating *)
        
        /\ philosophers' = [philosophers' EXCEPT ![p] = "thinking"]
        /\ forks' = [forks' EXCEPT ![p] = TRUE]
        /\ forks' = [forks'' EXCEPT ![ (p+1) % N ] = TRUE]
    end while
end process

end algorithm*)

Spec == 
    \E f \in SUBSET [0..N-1 -> BOOLEAN], p \in [0..N-1 -> {"thinking", "eating"}] :
        /\ forks = f
        /\ philosophers = p
        /\ \A i \in 0..N-1 : \/ p[i] = "thinking" \/ (p[i] = "eating" /\ f[i] = FALSE /\ f[(i+1) % N] = FALSE)
        /\ WF_philosopher

WF_philosopher == 
    \A p \in 0..N-1 :
        <>[] (philosophers[p] = "thinking" => <>(philosophers[p]' = "eating"))

Invariant ==
    \A i \in 0..N-1 : \/ philosophers[i] = "thinking" \/ (philosophers[i] = "eating" /\ forks[i] = FALSE /\ forks[(i+1) % N] = FALSE)
    /\ \A i, j \in 0..N-1 : i # j => ~ (philosophers[i] = "eating" /\ philosophers[j] = "eating" /\ (j = (i+1) % N \/ i = (j+1) % N))

=============================================================================