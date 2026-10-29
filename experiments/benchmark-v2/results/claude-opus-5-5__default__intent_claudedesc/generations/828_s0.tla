---------------------------- MODULE CatSearch ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES
    cat,
    box,
    dir,
    found,
    day

vars == <<cat, box, dir, found, day>>

Boxes == 1..N

Neighbors(b) == {x \in Boxes : x = b - 1 \/ x = b + 1}

StartBox == IF N >= 3 THEN 2 ELSE 1

MaxDays == IF N >= 3 THEN 2 * (N - 2) ELSE 2

NextBox(b, d) ==
    IF N <= 2 THEN 1
    ELSE IF d = "up"
         THEN IF b < N - 1 THEN b + 1 ELSE N - 1
         ELSE IF b > 2 THEN b - 1 ELSE 2

NextDir(b, d) ==
    IF N <= 2 THEN d
    ELSE IF d = "up"
         THEN IF b < N - 1 THEN "up" ELSE "down"
         ELSE IF b > 2 THEN "down" ELSE "up"

TypeOK ==
    /\ cat \in Boxes
    /\ box \in Boxes
    /\ dir \in {"up", "down"}
    /\ found \in BOOLEAN
    /\ day \in Nat

Init ==
    /\ cat \in Boxes
    /\ box = StartBox
    /\ dir = "up"
    /\ found = FALSE
    /\ day = 0

CheckHit ==
    /\ ~found
    /\ box = cat
    /\ found' = TRUE
    /\ UNCHANGED <<cat, box, dir, day>>

CheckMissAndCatMoves ==
    /\ ~found
    /\ box # cat
    /\ cat' \in Neighbors(cat)
    /\ box' = NextBox(box, dir)
    /\ dir' = NextDir(box, dir)
    /\ day' = day + 1
    /\ UNCHANGED found

Done ==
    /\ found
    /\ UNCHANGED vars

Next ==
    \/ CheckHit
    \/ CheckMissAndCatMoves
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(CheckHit \/ CheckMissAndCatMoves)

CatMovesToNeighbor ==
    [][~found /\ box # cat => cat' \in Neighbors(cat)]_vars

StrategySoundness ==
    ~found => day < MaxDays

BoundedSearch == day <= MaxDays

FoundIsCorrect == found => box = cat

GuaranteedCapture == <>found

Termination == <>[]found

=============================================================================