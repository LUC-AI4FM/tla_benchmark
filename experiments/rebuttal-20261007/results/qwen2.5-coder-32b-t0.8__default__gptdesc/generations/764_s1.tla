---- MODULE DiningPhilosophers ----

EXTENDS Naturals, Sequences, TLC

CONSTANTS N

VARIABLES sem, pc

Init == /\ sem = <<1, 1, 1, 1>>[1..N]
        /\ pc = [p \in {0 .. N-1} |-> "think"]

Next ==
    \/ \E p \in {0 .. N-1} :
        (pc[p] = "think" /\ sem[(p+1) % N] = 1)
            /\ (/\ IF p # 0 THEN
                        /\ sem[p] = 1
                        /\ pc' = [pc EXCEPT ![p] = "eat"]
                    ELSE
                        /\ sem[(N-1)] = 1
                        /\ pc' = [pc EXCEPT ![p] = "tryRightFork"]
                   FI
               /\ sem' = sem)
    \/ \E p \in {0 .. N-1} :
        (pc[p] = "eat" /\ UNCHANGED sem)
            /\ (/\ IF p # 0 THEN
                        /\ pc' = [pc EXCEPT ![p] = "releaseForks"]
                    ELSE
                        /\ pc' = [pc EXCEPT ![p] = "tryLeftFork"]
                   FI)
    \/ \E p \in {1 .. N-1} :
        (pc[p] = "tryRightFork" /\ sem[(p+1) % N] = 1)
            /\ (\* Acquire right fork *)
               /\ pc' = [pc EXCEPT ![p] = "tryLeftFork"]
               /\ sem' = [sem EXCEPT ![p] = 0]
    \/ \E p \in {1 .. N-1} :
        (pc[p] = "tryLeftFork" /\ sem[p] = 1)
            /\ (\* Acquire left fork *)
               /\ pc' = [pc EXCEPT ![p] = "eat"]
               /\ sem' = [sem EXCEPT ![p] = 0]
    \/ \E p \in {1 .. N-1} :
        (pc[p] = "releaseForks")
            /\ (\* Release both forks *)
               /\ pc' = [pc EXCEPT ![p] = "think"]
               /\ sem' = [sem EXCEPT ![p] = 1, ![(p+1) % N] = 1]
    \/ \E p \in {0} :
        (pc[p] = "tryLeftFork" /\ sem[(N-1)] = 1)
            /\ (\* Acquire left fork *)
               /\ pc' = [pc EXCEPT ![p] = "tryRightFork"]
               /\ sem' = [sem EXCEPT ![(N-1)] = 0]
    \/ \E p \in {0} :
        (pc[p] = "tryRightFork" /\ sem[0] = 1)
            /\ (\* Acquire right fork *)
               /\ pc' = [pc EXCEPT ![p] = "eat"]
               /\ sem' = [sem EXCEPT ![0] = 0]
    \/ \E p \in {0} :
        (pc[p] = "releaseForks")
            /\ (\* Release both forks *)
               /\ pc' = [pc EXCEPT ![p] = "think"]
               /\ sem' = [sem EXCEPT ![0] = 1, ![(N-1)] = 1]

Spec ==
    /\ Init
    /\ [][Next]_<<pc, sem>>
    /\ WF_<<pc>>[Next]
    /\ \A p \in {0 .. N-1} : SF_<<pc>>[pc[p] = "think"]
    /\ \A p \in {0 .. N-1}, q \in {(p+1) % N, (p-1) % N} :
        [](<>(pc[p] # "eat") \/ <>(pc[q] # "eat"))

====