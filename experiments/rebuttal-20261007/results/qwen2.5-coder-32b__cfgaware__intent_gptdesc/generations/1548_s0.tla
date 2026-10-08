------------------------------- MODULE ByzantineConsensus -------------------------------
CONSTANTS N, F, T

ASSUME N > 3 * T /\ T >= F

VARIABLES sentVotesCorrect, sentVotesFaulty, receivedVotes, proposal, decided, undecided

(* --algorithm ByzantineConsensus
variables 
    sentVotesCorrect = [p \in 1..N -> 0], 
    sentVotesFaulty = [p \in 1..N -> 0],
    receivedVotes = [p \in 1..N -> <<0, 0>>],
    proposal = [p \in 1..N -> ?],
    decided = [p \in 1..N -> FALSE],
    undecided = [p \in 1..N -> FALSE];

process CorrectProcess \in 1..(N-F)
begin
    with p \in 1..(N-F) do
        proposal[p] := CHOOSE v \in {0, 1};
        sentVotesCorrect[p] := 1;
        await decided[p] \/ undecided[p];
end process;

process FaultyProcess \in (N-F)+1..N
begin
    with p \in (N-F)+1..N do
        proposal[p] := CHOOSE v \in {0, 1};
        sentVotesFaulty[p] := 1;
        await decided[p] \/ undecided[p];
end process;

process Receiver \in 1..N
begin
    while TRUE do
        with p \in 1..N do
            if ~decided[p] /\ ~undecided[p] then
                receivedVotes[p] := <<receivedVotes[p][1] + sentVotesCorrect[p], receivedVotes[p][2] + sentVotesFaulty[p]>>;
                if receivedVotes[p][1] + receivedVotes[p][2] >= N - T then
                    if receivedVotes[p][1] >= N - T then
                        decided[p] := TRUE;
                    else if receivedVotes[p][2] >= N - T then
                        decided[p] := TRUE;
                    else
                        undecided[p] := TRUE;
                    end if;
                end if;
            end if;
        end with;
    end while;
end process;

end algorithm *)

TypeOK == /\ sentVotesCorrect \in [1..N -> 0..N]
          /\ sentVotesFaulty \in [1..N -> 0..N]
          /\ receivedVotes \in [1..N -> SUBSET {<<v, c>> \in [0..N] X [0..N] : v \in {0, 1} /\ c \in 0..N}]
          /\ proposal \in [1..N -> {0, 1}]
          /\ decided \in [1..N -> BOOLEAN]
          /\ undecided \in [1..N -> BOOLEAN]

OneStep0_Ltl == \/ CHANGING <<sentVotesCorrect, sentVotesFaulty, receivedVotes, proposal, decided, undecided>>
                \/ ~TypeOK

OneStep1_Ltl == \/ CHANGING <<sentVotesCorrect, sentVotesFaulty, receivedVotes, proposal, decided, undecided>>
                \/ ~TypeOK

AllDecideOne == \A p \in 1..(N-F) : decided[p] => (proposal[p] = 1)

Spec ==
    /\ TypeOK
    /\ WF_all([<<sentVotesCorrect, sentVotesFaulty, receivedVotes, proposal, decided, undecided>>]_<<CorrectProcess, FaultyProcess, Receiver>>)
    /\ SF_all([<<sentVotesCorrect, sentVotesFaulty, receivedVotes, proposal, decided, undecided>>]_<<Receiver>>)

=============================================================================