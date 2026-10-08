MODULE PCR

EXTENDS Naturals, TLC

CONSTANTS P0, T0

VARIABLES p, t, d, h, phase, temp

vars == <<p, t, d, h, phase, temp>>

TypeOK ==
    /\ p ∈ Nat
    /\ t ∈ Nat
    /\ d ∈ Nat
    /\ h ∈ Nat
    /\ phase ∈ {"HEAT", "COOL", "ANNEAL", "EXTEND"}
    /\ temp ∈ Nat

TotalConst == P0 + T0

Init ==
    /\ p = P0
    /\ t = T0
    /\ d = 0
    /\ h = 0
    /\ phase = "HEAT"
    /\ temp = 20

HeatStep ==
    /\ phase = "HEAT"
    /\ LET newTemp ∈ Nat == IF temp < 95 THEN temp + 1 ELSE temp IN
        /\ temp' = newTemp
        /\ phase' = IF newTemp = 95 THEN "COOL" ELSE "HEAT"
        /\ UNCHANGED <<p, t, d, h>>

CoolStep ==
    /\ phase = "COOL"
    /\ LET newTemp ∈ Nat == IF temp > 25 THEN temp - 1 ELSE temp IN
        /\ temp' = newTemp
        /\ phase' = IF newTemp = 25 THEN "ANNEAL" ELSE "COOL"
        /\ UNCHANGED <<p, t, d, h>>

AnnealStep ==
    /\ phase = "ANNEAL"
    /\ LET k ∈ 0..Min(p, t) IN
        /\ p' = p - k
        /\ t' = t - k
        /\ h' = h + k
        /\ phase' = "EXTEND"
        /\ UNCHANGED <<d, temp>>

ExtendStep ==
    /\ phase = "EXTEND"
    /\ d' = d + h
    /\ h' = 0
    /\ phase' = "HEAT"
    /\ UNCHANGED <<p, t, temp>>

Next == HeatStep \/ CoolStep \/ AnnealStep \/ ExtendStep

SafetySpec ==
    Init /\ []Next /\ []TypeOK /\ [](p + t + d + h = TotalConst)

LivenessProperty == <> (p = 0)

Spec == SafetySpec

=============================================================================