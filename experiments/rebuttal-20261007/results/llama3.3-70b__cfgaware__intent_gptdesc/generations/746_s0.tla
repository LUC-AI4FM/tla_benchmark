---------------------------- MODULE MeetingProtocol ----------------------------
EXTENDS Integers, TLC

CONSTANT M, N, Colors
VARIABLES agents, rendezvous, meetings, faded

TypeOK == 
  /\ M \in Nat && M > 0
  /\ N \in Nat && N > 0
  /\ Colors = {"Red", "Green", "Blue"}
  /\ agents \in [1..M -> Colors]
  /\ rendezvous \in (Subset([1..M]) \cup {<<>>})
  /\ meetings \in [1..M -> Nat]
  /\ faded \in Subset([1..M])

SumMet == 
  /\ TypeOK
  /\ meetings = [i \in 1..M |-> 0]

Spec ==
  /\ SumMet
  /\ [][
      /\ (rendezvous = <<>>)
        => (rendezvous' = <<>>) 
           \/ (\E i \in 1..M : 
               /\ agents[i] /= "Faded"
               /\ faded' = faded
               /\ rendezvous' = <<i>>
               /\ meetings' = meetings
               /\ UNCHANGED agents)
      /\ (rendezvous \in [1..M])
        => (rendezvous' = <<>>)
           \/ (\E j \in 1..M :
               /\ j /= rendezvous[1]
               /\ agents[j] /= "Faded"
               /\ faded' = faded
               /\ meetings' = [meetings EXCEPT ![i] = @ + 1, ![j] = @ + 1]
               /\ agents' = [agents EXCEPT 
                             ![rendezvous[1]] = Transition(agents[rendezvous[1]], agents[j]),
                             ![j] = Transition(agents[j], agents[rendezvous[1]])]
               /\ rendezvous' = <<>>)
      /\ (meetings = N)
        => (faded' = 1..M)
           \/ (\E i \in 1..M : 
               /\ faded' = faded \cup {i}
               /\ UNCHANGED agents
               /\ UNCHANGED meetings
               /\ rendezvous' = <<>>)
    ]

Transition(old, other) == 
  CASE old = "Red" -> 
    CASE other = "Red" -> "Green"
              [] other = "Green" -> "Blue"
              [] OTHER -> "Red"
  [] old = "Green" -> 
    CASE other = "Red" -> "Blue"
              [] other = "Green" -> "Red"
              [] OTHER -> "Green"
  [] OTHER -> 
    CASE other = "Red" -> "Green"
              [] other = "Green" -> "Blue"
              [] OTHER -> "Red"

=============================================================================