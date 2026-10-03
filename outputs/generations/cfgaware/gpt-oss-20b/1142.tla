MODULE RegionMapping
EXTENDS Naturals, Sequences

CONSTANT LOCATIONS, REGIONS, CODE

VARIABLES locs, regs, trans

(* Types *)
Loc    == Int
Region == [start : Int, end : Int]

(* Predicates and functions *)
IsWellFormedLoc(l) == l \in LOCATIONS

IsWellFormedReg(r) ==
  /\ r.start < r.end
  /\ r.start \in LOCATIONS
  /\ r.end   \in LOCATIONS

ParenthesisDepth(pos) ==
  LET depth(i) == IF CODE[i] = 40 THEN 1 ELSE IF CODE[i] = 41 THEN -1 ELSE 0 IN
  SUM i \in 1..pos : depth(i)

TokenPositions(r) ==
  { p \in r.start .. r.end :
      /\ CODE[p] # 32
      /\ (p = r.start \/ CODE[p-1] = 32) }

MapRegionToTokens(r) == TokenPositions(r)

WellFormedness ==
  /\ \A l \in locs : IsWellFormedLoc(l)
  /\ \A r \in regs : IsWellFormedReg(r)
  /\ \A r \in regs :
        \A pos \in r.start .. r.end :
            ParenthesisDepth(pos) >= 0

Ordering ==
  \A r1 \in regs, r2 \in regs :
      (r1 = r2) \/ (r1.end < r2.start \/ r2.end < r1.start)

Init == 
  /\ locs   = {}
  /\ regs   = {}
  /\ trans  = [r \in REGIONS |-> {}]

AddRegion(r) ==
  /\ IsWellFormedReg(r)
  /\ \A existing \in regs : existing.end < r.start \/ r.end < existing.start
  /\ r \notin regs
  /\ locs'   = locs   \cup {r.start, r.end}
  /\ regs'   = regs   \cup {r}
  /\ trans'  = [trans EXCEPT ![r] = TokenPositions(r)]

Next == \E r \in REGIONS : AddRegion(r) \/ UNCHANGED <<locs,regs,trans>>

Spec ==
  Init /\ [][Next]_<<locs,regs,trans>>

(* Invariants *)
Inv1 == \A r \in regs : IsWellFormedReg(r)
Inv2 == Ordering
Inv3 == \A r \in regs :
          \A pos \in r.start .. r.end :
              ParenthesisDepth(pos) >= 0

ASSERT Inv1
ASSERT Inv2
ASSERT Inv3

END MODULE