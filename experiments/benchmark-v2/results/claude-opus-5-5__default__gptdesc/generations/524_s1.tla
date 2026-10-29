------------------------------- MODULE ABQueue -------------------------------
EXTENDS Integers, Sequences

CONSTANTS Data, MaxQueueLen

ASSUME /\ Data # {}
       /\ MaxQueueLen \in Nat

Msgs == Data \X {0, 1}

Remove(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

(***************************************************************************
--algorithm ABQueue
variables AVar \in Msgs, BVar = AVar,
          AtoB = << >>, BtoA = << >>, queue = << >>;

fair process (ASnd = "ASnd")
begin a_snd: while TRUE do
               AtoB := Append(AtoB, AVar)
             end while
end process;

fair+ process (ARcv = "ARcv")
begin a_rcv: while TRUE do
               await BtoA # << >>;
               if Head(BtoA) = AVar /\ queue # << >> then
                 AVar := << Head(queue), 1 - AVar[2] >>;
                 queue := Tail(queue)
               end if;
               BtoA := Tail(BtoA)
             end while
end process;

fair process (BSnd = "BSnd")
begin b_snd: while TRUE do
               BtoA := Append(BtoA, BVar)
             end while
end process;

fair+ process (BRcv = "BRcv")
begin b_rcv: while TRUE do
               await AtoB # << >>;
               if Head(AtoB)[2] # BVar[2] then
                 BVar := Head(AtoB)
               end if;
               AtoB := Tail(AtoB)
             end while
end process;

process (LoseMsgs = "LoseMsgs")
begin lose: while TRUE do
              either with i \in 1..Len(AtoB) do
                       AtoB := Remove(i, AtoB)
                     end with
              or     with i \in 1..Len(BtoA) do
                       BtoA := Remove(i, BtoA)
                     end with
              end either
            end while
end process;

process (NewData = "NewData")
begin new_data: while TRUE do
                  await AVar = BVar /\ Len(queue) < MaxQueueLen;
                  with d \in Data do
                    queue := Append(queue, d)
                  end with
                end while
end process;
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES AVar, BVar, AtoB, BtoA, queue

vars == << AVar, BVar, AtoB, BtoA, queue >>

Init == /\ AVar \in Msgs
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>
        /\ queue = << >>

ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED << AVar, BVar, BtoA, queue >>

ARcv == /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar /\ queue # << >>
              THEN /\ AVar' = << Head(queue), 1 - AVar[2] >>
                   /\ queue' = Tail(queue)
              ELSE /\ UNCHANGED << AVar, queue >>
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED << BVar, AtoB >>

BSnd == /\ BtoA' = Append(BtoA, BVar)
        /\ UNCHANGED << AVar, BVar, AtoB, queue >>

BRcv == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
              THEN BVar' = Head(AtoB)
              ELSE UNCHANGED BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED << AVar, BtoA, queue >>

LoseMsgs == /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
                  /\ UNCHANGED BtoA
               \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
                  /\ UNCHANGED AtoB
            /\ UNCHANGED << AVar, BVar, queue >>

NewData == /\ AVar = BVar
           /\ Len(queue) < MaxQueueLen
           /\ \E d \in Data : queue' = Append(queue, d)
           /\ UNCHANGED << AVar, BVar, AtoB, BtoA >>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsgs \/ NewData

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ASnd)
        /\ WF_vars(ARcv) /\ SF_vars(ARcv)
        /\ WF_vars(BSnd)
        /\ WF_vars(BRcv) /\ SF_vars(BRcv)
\* END TRANSLATION

-----------------------------------------------------------------------------
TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs
          /\ AtoB \in Seq(Msgs)
          /\ BtoA \in Seq(Msgs)
          /\ queue \in Seq(Data)
          /\ Len(queue) <= MaxQueueLen

\* If the bits agree, the receiver holds exactly the sender's value.
Consistent == (AVar[2] = BVar[2]) => (AVar = BVar)

\* Every message in transit carries either the current or the previous value.
ChannelInv == /\ \A i \in 1..Len(AtoB) :
                    AtoB[i][2] = AVar[2] => AtoB[i] = AVar
              /\ \A i \in 1..Len(BtoA) :
                    BtoA[i][2] = BVar[2] => BtoA[i] = BVar

Inv == TypeOK /\ Consistent

\* Liveness: whenever the endpoints disagree, the receiver eventually catches up.
Progress == (AVar # BVar) ~> (AVar = BVar)

THEOREM Spec => []Inv
THEOREM Spec => Progress
=============================================================================