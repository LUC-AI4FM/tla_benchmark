MODULE TwoProcLock
EXTENDS Naturals

CONSTANTS P1, P2

VARIABLE lock, state1, state2

(*--algorithm MutualExclusion
  variables lock = 0, state1 = "nc", state2 = "nc"
  
  process p1 {
    repeat
      state1 := "nc";
      if (lock = 0) then
        lock := P1;
        state1 := "l1";
      end if;
      if (state1 = "l1") then
        state1 := "cs";
      end if;
      if (state1 = "cs") then
        lock := 0;
        state1 := "nc";
      end if;
    end repeat;
  }
  
  process p2 {
    repeat
      state2 := "nc";
      if (lock = 0) then
        lock := P2;
        state2 := "l1";
      end if;
      if (state2 = "l1") then
        state2 := "cs";
      end if;
      if (state2 = "cs") then
        lock := 0;
        state2 := "nc";
      end if;
    end repeat;
  }
--*)

Init ==
  /\ lock = 0
  /\ state1 = "nc"
  /\ state2 = "nc"

p1Acquire ==
  /\ state1 = "nc"
  /\ lock = 0
  /\ state1' = "l1"
  /\ lock' = P1
  /\ state2' = state2

p1ToCS ==
  /\ state1 = "l1"
  /\ state1' = "cs"
  /\ lock' = lock
  /\ state2' = state2

p1Exit ==
  /\ state1 = "cs"
  /\ state1' = "nc"
  /\ lock' = 0
  /\ state2' = state2

p2Acquire ==
  /\ state2 = "nc"
  /\ lock = 0
  /\ state2' = "l1"
  /\ lock' = P2
  /\ state1' = state1

p2ToCS ==
  /\ state2 = "l1"
  /\ state2' = "cs"
  /\ lock' = lock
  /\ state1' = state1

p2Exit ==
  /\ state2 = "cs"
  /\ state2' = "nc"
  /\ lock' = 0
  /\ state1' = state1

Next == p1Acquire \/ p1ToCS \/ p1Exit \/ p2Acquire \/ p2ToCS \/ p2Exit

Spec == Init /\ [][Next]_<<lock, state1, state2>>

MutualExclusion ==
  ~(state1 = "cs" /\ state2 = "cs")

Process1Liveliness ==
  [] (state1 = "l1" => <> state1 = "cs")