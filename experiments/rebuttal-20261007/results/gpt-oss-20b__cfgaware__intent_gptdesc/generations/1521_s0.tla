------------------------------ MODULE CoffeeCan ------------------------------
EXTENDS Naturals

CONSTANTS InitWhite, InitBlack

VARIABLES w, b

(* ------------------------------------------------------------------ *)
(* State invariants: bean counts are non‑negative integers             *)
StateInv == w >= 0 /\ b >= 0

(* Initial condition – any finite non‑zero total number of beans       *)
Init == StateInv
        /\ w = InitWhite
        /\ b = InitBlack
        /\ InitWhite + InitBlack > 0

(* ------------------------------------------------------------------ *)
(* Transition relation: two beans are removed and the container is   *)
(* updated according to the rule described in the problem statement. *)
Next ==
    \/ (\E w' : w >= 2          /\ w' = w - 2      /\ b' = b + 1)
    \/ (\E b' : b >= 2          /\ w' = w           /\ b' = b - 1)
    \/ (\E w',b' : w >= 1 /\ b >= 1
            /\ w' = w           /\ b' = b - 1)

(* ------------------------------------------------------------------ *)
(* Safety property: each transition decreases the total number of     *)
(* beans by exactly one.                                               *)
Safety == \A w,b,w',b' : (Next => (w + b) - (w' + b') = 1)

(* Termination property: eventually at most one bean remains.        *)
Termination == []<> (w + b <= 1)

(* Parity invariant of white beans – preserved by every transition.   *)
ParityInvariant == \A w,b,w',b' : (Next => Mod(w,2) = Mod(w',2))

(* Final‑state characterization: the color of the single remaining bean *)
(* is determined solely by the initial parity of white beans.           *)
THEOREM FinalColor ==
    \A w,b :
        ((w + b = 1) =>
            (w = 1 <=> Mod(InitWhite,2) = 1))

(* ------------------------------------------------------------------ *)
(* The complete specification: initial condition and temporal          *)
(* evolution under the transition relation. Fairness assumptions may   *)
(* be added in the model‑checking configuration to rule out           *)
(* pathological infinite deferral of enabled transitions.             *)
Spec == Init /\ [][Next]_{<<w,b>>}

============================================================================