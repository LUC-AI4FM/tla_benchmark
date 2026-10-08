------------------------------- MODULE RendezvousProtocol -------------------------------

CONSTANTS M, N \* Number of agents and meeting budget

ASSUME M > 0 /\ N > 0

VARIABLES states, meetings, rendezvous, globalMeetings

\* Initial state: each agent has one of three colors (represented as 1, 2, or 3), 
\* no meetings have occurred, the rendezvous is empty, and the global meeting counter is zero.
Init == /\ states \in [1..M -> {1, 2, 3}]
        /\ meetings \in [1..M -> 0]
        /\ rendezvous = << >>
        /\ globalMeetings = 0

\* A symmetric function that updates the state of two agents based on their current states.
\* This is an abstract function and should be defined externally or through assumptions.
VARIABLES colorTransition
ASSUME \A s1, s2 \in {1, 2, 3} : colorTransition[s1][s2] = colorTransition[s2][s1]

\* Action: An agent arrives at the rendezvous point.
Arrive(agent) == 
    /\ agent \in 1..M
    /\ rendezvous = << >>
    /\ globalMeetings < N
    /\ meetings[agent] < N
    /\ states[agent] # 0
    /\ \/ /\ rendezvous' = <<agent>>
       /\ states' = [states EXCEPT ![agent] = states[agent]]
       /\ meetings' = [meetings EXCEPT ![agent] = meetings[agent]]
       /\ globalMeetings' = globalMeetings

\* Action: Two agents meet at the rendezvous point.
Meet ==
    /\ \E agent1, agent2 \in 1..M : 
        (rendezvous = <<agent1>> /\ states[agent1] # 0 /\ states[agent2] # 0)
    /\ LET agent1 == rendezvous[1]
       agent2 == CHOOSE a \in 1..M : a # agent1 /\ states[a] # 0
    IN /\ states' = [states EXCEPT ![agent1] = colorTransition[states[agent1]][states[agent2]],
                             ![agent2] = colorTransition[states[agent2]][states[agent1]]]
       /\ meetings' = [meetings EXCEPT ![agent1] = meetings[agent1] + 1,
                              ![agent2] = meetings[agent2] + 1]
       /\ globalMeetings' = globalMeetings + 1
       /\ rendezvous' = << >>

\* Action: An agent becomes inactive (faded) once the meeting budget is reached.
Fade(agent) ==
    /\ agent \in 1..M
    /\ states[agent] # 0
    /\ globalMeetings >= N
    /\ \/ meetings[agent] < N
       \/ meetings[agent] = N /\ rendezvous = <<agent>>
    /\ states' = [states EXCEPT ![agent] = 0]
    /\ meetings' = meetings
    /\ globalMeetings' = globalMeetings
    /\ rendezvous' = IF rendezvous = <<agent>> THEN << >> ELSE rendezvous

\* Next state relation.
Next == \/ \E agent \in 1..M : Arrive(agent)
        \/ Meet
        \/ \E agent \in 1..M : Fade(agent)

Spec == Init /\ [][Next]_<<states, meetings, rendezvous, globalMeetings>>

TypeOK ==
    /\ states \in [1..M -> {0, 1, 2, 3}]
    /\ meetings \in [1..M -> 0..N]
    /\ rendezvous \in SUBSET (1..M) \* Rendezvous can hold at most one agent
    /\ globalMeetings \in 0..N

SumMet ==
    LET totalMeetings == SUM {meetings[a] : a \in 1..M}
    IN \/ globalMeetings < N
       \/ globalMeetings = N /\ totalMeetings = 2*N

=====================================================================================