------------------------------- MODULE RendezvousProtocol -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS M, N
ASSUME M \in Nat /\ M > 0
ASSUME N \in Nat /\ N > 0

VARIABLES agents, rendezvous, meetingCount, globalMeetings

(* --algorithm RendezvousProtocol
variables 
    agents = [i \in 1..M -> {red, green, blue}],
    rendezvous = <<>>,
    meetingCount = [i \in 1..M -> 0],
    globalMeetings = 0;

fair process (Agent \in 1..M)
vars nextColor
begin
    while agents[Agent] /= "faded" do
        if rendezvous = <<>> then
            rendezvous := <<Agent>>;
        else
            let otherAgent = rendezvous[1] in
                assert otherAgent \in 1..M;
                nextColor := ColorTransition(agents[Agent], agents[otherAgent]);
                agents := [agents EXCEPT ![Agent] = nextColor, ![otherAgent] = nextColor];
                meetingCount := [meetingCount EXCEPT ![Agent] = meetingCount[Agent] + 1, ![otherAgent] = meetingCount[otherAgent] + 1];
                globalMeetings := globalMeetings + 1;
                rendezvous := <<>>;
        end if;
    end while;
end process;

end algorithm *)

Init == /\ agents \in [1..M -> {"red", "green", "blue"}]
        /\ rendezvous = <<>>
        /\ meetingCount \in [1..M -> {0}]
        /\ globalMeetings = 0

Next ==
    LET Agent == CHOOSE a \in 1..M: TRUE
    IN
    \/ /\ rendezvous = <<>>
       /\ agents[Agent] /= "faded"
       /\ rendezvous' = <<Agent>>
       /\ UNCHANGED <<agents, meetingCount, globalMeetings>>
    \/ /\ rendezvous /= <<>>
       /\ LET otherAgent == rendezvous[1]
          IN
          /\ agents[otherAgent] /= "faded"
          /\ agents[Agent] /= "faded"
          /\ \E nextColor \in {"red", "green", "blue"}:
             agents' = [agents EXCEPT ![Agent] = nextColor, ![otherAgent] = nextColor]
          /\ meetingCount' = [meetingCount EXCEPT ![Agent] = meetingCount[Agent] + 1, ![otherAgent] = meetingCount[otherAgent] + 1]
          /\ globalMeetings' = globalMeetings + 1
          /\ rendezvous' = <<>>
       /\ UNCHANGED agents[EXCEPT ![Agent], ![otherAgent]]
    \/ /\ globalMeetings >= N
       /\ agents' = [agents EXCEPT ![Agent] = "faded"]
       /\ UNCHANGED <<rendezvous, meetingCount, globalMeetings>>

Spec ==
    Init /\ [][Next]_<<agents, rendezvous, meetingCount, globalMeetings>> /\ WF_next(<<agents, rendezvous, meetingCount, globalMeetings>>)

Safety ==
    /\ \A i \in 1..M: agents[i] = "faded" \/ meetingCount'[i] = meetingCount[i]
    /\ \A i \in 1..M: agents[i] = "faded" \/ agents'[i] \in {"red", "green", "blue"}
    /\ globalMeetings' <= N
    /\ (rendezvous = <<>> \/ rendezvous' = <<>>)

Termination ==
    /\ globalMeetings >= N
    /\ \A i \in 1..M: agents[i] = "faded" \/ meetingCount'[i] = meetingCount[i]

AccountingInvariant ==
    /\ globalMeetings < N \/ (\E sum \in Nat: \A i \in 1..M: meetingCount[i] + meetingCount'[i] = sum)
    /\ (globalMeetings >= N) => (\E sum \in Nat: \A i \in 1..M: meetingCount[i] = sum / 2)

Spec ==
    Init /\ [][Next]_<<agents, rendezvous, meetingCount, globalMeetings>> /\ WF_next(<<agents, rendezvous, meetingCount, globalMeetings>>) 
        /\ Spec => []Safety
        /\ Spec => []Termination
        /\ Spec => []AccountingInvariant

ColorTransition(c1, c2) == CHOOSE c \in {"red", "green", "blue"}: TRUE  (* Abstract color transition function *)

=============================================================================