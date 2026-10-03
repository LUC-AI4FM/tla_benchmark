---------------------------- MODULE DieHard ----------------------------
EXTENDS Integers, TLC

CONSTANTS SmallJugCapacity, BigJugCapacity
VARIABLES smallJug, bigJug, waterUsage

WaterActions == {"fillSmall", "fillBig", "emptySmall", "emptyBig", "pourSmallToBig", "pourBigToSmall"}
Next(s) ==
  \/ (s.smallJug < SmallJugCapacity) /\ s' = [s smallJug |-> SmallJugCapacity]
  \/ (s.bigJug < BigJugCapacity) /\ s' = [s bigJug |-> BigJugCapacity]
  \/ (s.smallJug > 0) /\ s' = [s smallJug |-> 0]
  \/ (s.bigJug > 0) /\ s' = [s bigJug |-> 0]
  \/ (s.smallJug > 0 /\ s.bigJug < BigJugCapacity) /\ 
      s' = [s smallJug |-> Max(0, s.smallJug - (BigJugCapacity - s.bigJug)), 
             bigJug |-> Min(BigJugCapacity, s.bigJug + s.smallJug)]
  \/ (s.bigJug > 0 /\ s.smallJug < SmallJugCapacity) /\ 
      s' = [s smallJug |-> Min(SmallJugCapacity, s.smallJug + s.bigJug), 
             bigJug |-> Max(0, s.bigJug - (SmallJugCapacity - s.smallJug))]

NextWaterUsage(w) == w + 1

Init ==
  /\ smallJug = 0
  /\ bigJug = 0
  /\ waterUsage = 0

Spec == Init /\ [][Next(_)]

THEOREM Spec => <>[](bigJug = 4)
THEOREM TLC.PrintStats
THEOREM TLC.PrintStateGraph
THEOREM waterUsage > 10 => (smallJug # 0 \/ bigJug # 0)

=============================================================================