------------------------------- MODULE MutualExclusion -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES intent, tour1, tour2, state

(* --algorithm mutual_exclusion
variables 
    intent = [p \in 1..N -> FALSE],
    tour1 = 0,
    tour2 = 0,
    state = [p \in 1..N -> "idle"];

process (p \in 1..N)
begin
Entry:
    while TRUE do
        intent[p] := TRUE;
        tour1 := p;
        await tour2 = 0;
        tour2 := p;
        if (\A q \in 1..N \ {p}: intent[q] => q <= p) then
            break;
        else
            tour2 := 0;
            intent[p] := FALSE;
        end if;
    end while;

InCS:
    state[p] := "critical";
    skip; (* Critical section *)
    state[p] := "idle";

Exit:
    tour2 := 0;
    intent[p] := FALSE;
end process;
end algorithm *)

Init == /\ intent = [p \in 1..N -> FALSE]
        /\ tour1 = 0
        /\ tour2 = 0
        /\ state = [p \in 1..N -> "idle"]

Next ==
    \/ \E p \in 1..N: 
        (state[p] = "idle" /\
         intent' = [intent EXCEPT ![p] = TRUE] /\
         tour1' = p /\
         tour2' = 0 /\
         state' = state)
    \/ \E p \in 1..N:
        (state[p] = "idle" /\ tour2 = 0 /\
         intent' = intent /\
         tour1' = tour1 /\
         tour2' = p /\
         state' = state)
    \/ \E p \in 1..N:
        (state[p] = "idle" /\ tour2 = p /\ (\A q \in 1..N \ {p}: intent[q] => q <= p) /\
         intent' = intent /\
         tour1' = tour1 /\
         tour2' = tour2 /\
         state' = [state EXCEPT ![p] = "critical"])
    \/ \E p \in 1..N:
        (state[p] = "idle" /\ tour2 = p /\ (\E q \in 1..N \ {p}: intent[q] /\ q > p) /\
         intent' = [intent EXCEPT ![p] = FALSE] /\
         tour1' = tour1 /\
         tour2' = 0 /\
         state' = state)
    \/ \E p \in 1..N:
        (state[p] = "critical" /\
         intent' = intent /\
         tour1' = tour1 /\
         tour2' = 0 /\
         state' = [state EXCEPT ![p] = "idle"])

Spec ==
    /\ Init
    /\ [][Next]_<<intent, tour1, tour2, state>>
    /\ WF_next(<<intent, tour1, tour2, state>>)

MutualExclusion == \A p, q \in 1..N: p # q => [](state[p] = "critical" => state[q] # "critical")

Liveness ==
    \/ \E p \in 1..N: WFState(p, "idle")
    \/ \E p \in 1..N: SFState(p, "critical")

WFState(p, s) == <<p>> \in WFState_(s)

SFState(p, s) == <<p>> \in SFState_(s)

WFState_(s) == {ps \in Seq(1..N): \A i \in 1..Len(ps): state[ps[i]] = s}

SFState_(s) == {ps \in Seq(1..N): \E i \in 1..Len(ps): state[ps[i]] = s}
=============================================================================