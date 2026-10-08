------------------------------- MODULE MutualExclusionLock -------------------------------
EXTENDS Integers, TLC

CONSTANTS P1, P2

VARIABLES lock, p1_loc, p2_loc

(* --algorithm mutual_exclusion_lock
variables 
    lock = FALSE,
    p1_loc = "non_critical",
    p2_loc = "non_critical";

process (P1 \in {P1})
begin
  while TRUE do
    await p1_loc = "non_critical";
    p1_loc := "waiting";
    await lock = FALSE;
    lock := TRUE;
    p1_loc := "critical";
    await p1_loc = "critical";
    p1_loc := "post_critical";
    await p1_loc = "post_critical";
    lock := FALSE;
    p1_loc := "non_critical"
  end while
end process;

process (P2 \in {P2})
begin
  while TRUE do
    await p2_loc = "non_critical";
    p2_loc := "waiting";
    await lock = FALSE;
    lock := TRUE;
    p2_loc := "critical";
    await p2_loc = "critical";
    p2_loc := "post_critical";
    await p2_loc = "post_critical";
    lock := FALSE;
    p2_loc := "non_critical"
  end while
end process;

end algorithm *)

Init == /\ lock = FALSE 
        /\ p1_loc = "non_critical" 
        /\ p2_loc = "non_critical"

Next ==
    \/ /\ p1_loc = "non_critical"
       /\ p2_loc \notin {"critical", "post_critical"}
       /\ 'p1_loc' = "waiting"
       /\ UNCHANGED <<lock, p2_loc>>
    \/ /\ p1_loc = "waiting"
       /\ lock = FALSE
       /\ 'p1_loc' = "critical"
       /\ 'lock' = TRUE
       /\ UNCHANGED p2_loc
    \/ /\ p1_loc = "critical"
       /\ 'p1_loc' = "post_critical"
       /\ UNCHANGED <<lock, p2_loc>>
    \/ /\ p1_loc = "post_critical"
       /\ 'p1_loc' = "non_critical"
       /\ 'lock' = FALSE
       /\ UNCHANGED p2_loc
    \/ /\ p2_loc = "non_critical"
       /\ p1_loc \notin {"critical", "post_critical"}
       /\ 'p2_loc' = "waiting"
       /\ UNCHANGED <<lock, p1_loc>>
    \/ /\ p2_loc = "waiting"
       /\ lock = FALSE
       /\ 'p2_loc' = "critical"
       /\ 'lock' = TRUE
       /\ UNCHANGED p1_loc
    \/ /\ p2_loc = "critical"
       /\ 'p2_loc' = "post_critical"
       /\ UNCHANGED <<lock, p1_loc>>
    \/ /\ p2_loc = "post_critical"
       /\ 'p2_loc' = "non_critical"
       /\ 'lock' = FALSE
       /\ UNCHANGED p1_loc

Spec == Init /\ [][Next]_<<lock, p1_loc, p2_loc>>

TypeInvariant ==
    /\ lock \in {FALSE, TRUE}
    /\ p1_loc \in {"non_critical", "waiting", "critical", "post_critical"}
    /\ p2_loc \in {"non_critical", "waiting", "critical", "post_critical"}

MutualExclusionInvariant ==
    /\ \/ p1_loc \notin {"critical", "post_critical"} 
       \/ p2_loc \notin {"critical", "post_critical"}
    /\ (lock = TRUE) => ((p1_loc \in {"critical", "post_critical"}) <=> (p2_loc \notin {"critical", "post_critical"}))

Inv == TypeInvariant /\ MutualExclusionInvariant

THEOREM Spec => []Inv
=============================================================================