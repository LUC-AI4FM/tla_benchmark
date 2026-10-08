------------------------------- MODULE PCR -------------------------------

CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid

(* --algorithm PCR
variables 
    tee = "Hot",
    primer = PRIMER,
    dna = DNA,
    template = 0,
    hybrid = 0;
{
    while TRUE do
        if tee = "Hot" then
            either
                heat:
                    \* Transition from "Hot" to "TooHot"
                    tee := "TooHot";
                    template := template + dna + hybrid;
                    dna := 0;
                    primer := primer + hybrid;
                    hybrid := 0;
            or
                anneal:
                    \* Transition from "Hot" to "Warm"
                    tee := "Warm";
                    let p = CHOOSE p \in 1..primer : TRUE,
                        t = CHOOSE t \in 1..template : TRUE in
                    primer := primer - p;
                    template := template - t;
                    hybrid := hybrid + p;
            end either
        else if tee = "TooHot" then
            cool:
                \* Transition from "TooHot" to "Hot"
                tee := "Hot";
        else if tee = "Warm" then
            extend:
                \* Transition from "Warm" to "Hot"
                tee := "Hot";
                dna := dna + hybrid;
                hybrid := 0;
        end if;
    end while;
}
end algorithm *)

TypeOK == \/ tee = "Hot"
          \/ tee = "TooHot"
          \/ tee = "Warm"

primerPositive == primer >= 0

preservationInvariant ==
    /\ template \in Nat
    /\ dna \in Nat
    /\ hybrid \in Nat
    /\ primer \in Nat
    /\ template + primer + 2*(dna + hybrid) = PRIMER + 2*DNA

preservationProperty == []<>(template + primer + 2*(dna + hybrid) = PRIMER + 2*DNA)

Spec ==
    /\ TypeOK
    /\ primerPositive
    /\ preservationInvariant
    /\ preservationProperty
    /\ WF_vars(<<heat, cool, anneal, extend>>)

WF_vars(seq) == \A s \in State: \E i \in 1..Len(seq):
                    LET act = seq[i] IN
                        \/ act \notin Enabled(s)
                        \/ \E s' \in NextState(act, s): WF_vars(<<seq[EXCEPT ![i] = act]>>)

Enabled(action) ==
    CASE action = heat   -> tee = "Hot"
    [] action = cool   -> tee = "TooHot"
    [] action = anneal -> tee = "Hot" /\ primer > 0 /\ template > 0
    [] action = extend -> tee = "Warm"

NextState(action, s) ==
    CASE action = heat ->
        LET new_tee = "TooHot"
            new_template = s.template + s.dna + s.hybrid
            new_dna = 0
            new_primer = s.primer + s.hybrid
            new_hybrid = 0
        IN { [s EXCEPT !.tee = new_tee, !.template = new_template,
                 !.dna = new_dna, !.primer = new_primer, !.hybrid = new_hybrid] }
    [] action = cool ->
        LET new_tee = "Hot"
        IN { [s EXCEPT !.tee = new_tee] }
    [] action = anneal ->
        LET p = CHOOSE p \in 1..s.primer : TRUE
            t = CHOOSE t \in 1..s.template : TRUE
            new_tee = "Warm"
            new_primer = s.primer - p
            new_template = s.template - t
            new_hybrid = s.hybrid + p
        IN { [s EXCEPT !.tee = new_tee, !.primer = new_primer,
                 !.template = new_template, !.hybrid = new_hybrid] }
    [] action = extend ->
        LET new_tee = "Hot"
            new_dna = s.dna + s.hybrid
            new_hybrid = 0
        IN { [s EXCEPT !.tee = new_tee, !.dna = new_dna, !.hybrid = new_hybrid] }

=============================================================================