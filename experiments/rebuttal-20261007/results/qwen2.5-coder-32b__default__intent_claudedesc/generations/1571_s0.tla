------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N >= 2

VARIABLES forks, state

(* --algorithm dining_philosophers
variables
    forks = <<1, 1, 1, 1>>,  (* 1 means fork is available *)
    state = <<'thinking', 'thinking', 'thinking', 'thinking'>>;  (* 'thinking' or 'eating' *)

process Philosopher \in 0..N-1
begin
    while TRUE do
        if \A i \in 0..N-1 : state[i] = "thinking" then
            if self = 0 then
                await(forks[self] = 1);
                forks := [forks EXCEPT ![self] = 0];
                await(forks[(self + N - 1) % N] = 1);
                forks := [forks EXCEPT ![(self + N - 1) % N] = 0];
            else
                await(forks[self] = 1);
                forks := [forks EXCEPT ![self] = 0];
                await(forks[(self + 1) % N] = 1);
                forks := [forks EXCEPT ![(self + 1) % N] = 0];
            end if;
            state := [state EXCEPT ![self] = "eating"];
            skip;  (* eat *)
            state := [state EXCEPT ![self] = "thinking"];
            forks := [forks EXCEPT ![self] = 1, ![(self + 1) % N] = 1];
        end if;
    end while;
end process;

end algorithm *)

Init == /\ forks = <<1, 1, 1, 1>>
        /\ state = <<'thinking', 'thinking', 'thinking', 'thinking'>>

Next ==
    \E self \in 0..N-1 :
        LET right_fork == (self + 1) % N
            left_fork  == (self + N - 1) % N
        IN
        \/ /\ state[self] = "thinking"
           /\ (\A i \in 0..N-1 : state[i] = "thinking")
           /\ (self = 0 -> forks[left_fork] = 1)
           /\ (self = 0 -> forks[right_fork] = 1)
           /\ (self # 0 -> forks[self] = 1)
           /\ (self # 0 -> forks[right_fork] = 1)
           /\ forks' = [forks EXCEPT ![left_fork] = IF self = 0 THEN 0 ELSE forks[left_fork],
                                   ![right_fork] = 0]
           /\ state' = [state EXCEPT ![self] = "eating"]
        \/ /\ state[self] = "eating"
           /\ state' = [state EXCEPT ![self] = "thinking"]
           /\ forks' = [forks EXCEPT ![self] = 1, ![right_fork] = 1]

Spec ==
    WF_next(Init, Next) /\
    \A i \in 0..N-1 : [](<>[] state[i] = "eating") /\
    \A i \in 0..N-1, j \in {i, (i + 1) % N} : []\A s \in State : ~(\E k \in 0..N-1 : s.state[k] = "eating" /\ k # i /\ k # j)

=============================================================================