------------------------------- MODULE DiningPhilosophers -------------------------------
CONSTANTS N

VARIABLES sem, pc

(*--algorithm dining_philosophers
variables 
    sem = <<1, 1, 1, 1>>,  \* Initialize semaphores to 1 (available)
    pc = [i \in 0..N-1 |-> "think"]  \* Initialize all philosophers to thinking

process Philosopher \in 0..N-1
begin
    while TRUE do
        if self = 0 then
            \* Philosopher 0 picks up the left fork first to break symmetry
            await sem[N-1] = 1;
            sem[N-1] := 0;  \* Pick up left fork
            await sem[0] = 1;
            sem[0] := 0;  \* Pick up right fork
        else
            \* Other philosophers pick up the right fork first
            await sem[self] = 1;
            sem[self] := 0;  \* Pick up right fork
            await sem[(self-1) % N] = 1;
            sem[(self-1) % N] := 0;  \* Pick up left fork
        end if;

        pc[self] := "eat";  \* Eat

        \* Release both forks in the reverse order of acquisition
        if self = 0 then
            sem[0] := 1;  \* Put down right fork
            sem[N-1] := 1;  \* Put down left fork
        else
            sem[(self-1) % N] := 1;  \* Put down left fork
            sem[self] := 1;  \* Put down right fork
        end if;

        pc[self] := "think";  \* Think
    end while;
end process

end algorithm*)

Spec == /\ Init
        /\ [][Next]_<<sem, pc>>
        /\ WF_pc(Act)

Init == /\ sem = <<1, 1, 1, 1>>
        /\ pc = [i \in 0..N-1 |-> "think"]

Next == \/ \E i \in 0..N-1 : pc[i] = "think" /\ AcquireForks(i)
         \/ \E i \in 0..N-1 : pc[i] = "eat" /\ ReleaseForks(i)

AcquireForks(i) ==
    LET right_fork == i
        left_fork  == (i - 1) % N
    IN
        IF i = 0 THEN
            /\ sem[N-1] = 1
            /\ sem' = [sem EXCEPT ![N-1] = 0]
            /\ sem[left_fork] = 1
            /\ sem'' = [sem' EXCEPT ![left_fork] = 0]
        ELSE
            /\ sem[right_fork] = 1
            /\ sem' = [sem EXCEPT ![right_fork] = 0]
            /\ sem[left_fork] = 1
            /\ sem'' = [sem' EXCEPT ![left_fork] = 0]
        ENDIF
        /\ pc' = [pc EXCEPT ![i] = "eat"]

ReleaseForks(i) ==
    LET right_fork == i
        left_fork  == (i - 1) % N
    IN
        IF i = 0 THEN
            /\ sem'' = [sem EXCEPT ![0] = 1]
            /\ sem''' = [sem'' EXCEPT ![N-1] = 1]
        ELSE
            /\ sem'' = [sem EXCEPT ![(i - 1) % N] = 1]
            /\ sem''' = [sem'' EXCEPT ![i] = 1]
        ENDIF
        /\ pc' = [pc EXCEPT ![i] = "think"]

Act == {AcquireForks(i), ReleaseForks(i) : i \in 0..N-1}

WF_pc(action) ==
    /\ \A i \in 0..N-1 : WF_vars(pc, action, {"think", "eat"}, i)

Invariant ==
    \A i \in 0..N-1 :
        \/ pc[i] # "eat"
        \/ (pc[(i + 1) % N] # "eat")

StarvationFree ==
    \A i \in 0..N-1 : <>[]<>(pc[i] = "eat")
================================================================================