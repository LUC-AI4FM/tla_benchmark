------------------------------- MODULE MutualExclusionLock -------------------------------

CONSTANTS PC1, PC2, CRITICAL, EXIT, TURN0, TURN1, STUTTER

VARIABLES pc1, pc2, turn, history, stuttering

(*--algorithm mutual_exclusion_lock
variables 
    pc1 \in {PC1, PC2, CRITICAL, EXIT},
    pc2 \in {PC1, PC2, CRITICAL, EXIT},
    turn \in {TURN0, TURN1},
    history \subseteq {TURN0, TURN1},
    stuttering \in BOOLEAN;

process (P1 \in {1})
begin
  while TRUE do
    await pc1 = PC1;
    if stuttering then
      stuttering := FALSE;
    else
      turn := TURN0;
      history := history \cup {TURN0};
      pc1 := PC2;
    end if;

    await pc1 = PC2;
    if stuttering then
      stuttering := FALSE;
    else
      while (pc2 = CRITICAL) /\ (turn = TURN0) do
        stuttering := TRUE;
      end while;
      pc1 := CRITICAL;
    end if;

    await pc1 = CRITICAL;
    pc1 := EXIT;

    await pc1 = EXIT;
    pc1 := PC1;
end process;

process (P2 \in {2})
begin
  while TRUE do
    await pc2 = PC1;
    if stuttering then
      stuttering := FALSE;
    else
      turn := TURN1;
      history := history \cup {TURN1};
      pc2 := PC2;
    end if;

    await pc2 = PC2;
    if stuttering then
      stuttering := FALSE;
    else
      while (pc1 = CRITICAL) /\ (turn = TURN1) do
        stuttering := TRUE;
      end while;
      pc2 := CRITICAL;
    end if;

    await pc2 = CRITICAL;
    pc2 := EXIT;

    await pc2 = EXIT;
    pc2 := PC1;
end process;
end algorithm*)

SpecHS == /\ pc1 \in {PC1, PC2, CRITICAL, EXIT}
           /\ pc2 \in {PC1, PC2, CRITICAL, EXIT}
           /\ turn \in {TURN0, TURN1}
           /\ history \subseteq {TURN0, TURN1}
           /\ stuttering \in BOOLEAN

TypeOKHS == SpecHS

InvHS == \/ (pc1 = CRITICAL) => ((turn = TURN0) <=> (history = {TURN0}))
         \/ (pc2 = CRITICAL) => ((turn = TURN1) <=> (history = {TURN1}))

LockInv == /\ InvHS
           /\ ~((pc1 = CRITICAL) /\ (pc2 = CRITICAL))

Spec == SpecHS /\ LockInv

PSpec == Spec

=============================================================================