MODULE PCR
EXTENDS Naturals

CONSTANTS initDS, initSS, initPrimers

VARIABLES phase, ds, ss, primers, hybrids

PhaseDenature == "Denature"
PhaseAnneal   == "Anneal"
PhaseExtend   == "Extend"

Total == 2*initDS + initSS + initPrimers

Init ==
    /\ phase = PhaseDenature
    /\ ds = initDS
    /\ ss = initSS
    /\ primers = initPrimers
    /\ hybrids = 0

NonNeg ==
    /\ ds >= 0
    /\ ss >= 0
    /\ primers >= 0
    /\ hybrids >= 0

Conservation ==
    2*ds + ss + primers + 2*hybrids = Total

DenatureAction ==
    /\ phase = PhaseDenature
    /\ LET oldDS == ds, oldHybrids == hybrids,
         oldPrimers == primers, oldSS == ss IN
        /\ phase' = PhaseAnneal
        /\ ds' = 0
        /\ hybrids' = 0
        /\ ss' = oldSS + 2*oldDS + oldHybrids
        /\ primers' = oldPrimers + oldHybrids

AnnealAction ==
    /\ phase = PhaseAnneal
    /\ LET k == CHOOSE n \in Nat : (n <= \min(ss, primers)) IN
        /\ phase' = PhaseExtend
        /\ ss' = ss - k
        /\ primers' = primers - k
        /\ hybrids' = hybrids + k
        /\ ds' = ds

ExtendAction ==
    /\ phase = PhaseExtend
    /\ LET newDS == hybrids IN
        /\ phase' = PhaseDenature
        /\ ds' = ds + newDS
        /\ hybrids' = 0
        /\ ss' = ss
        /\ primers' = primers

Next ==
    DenatureAction \/ AnnealAction \/ ExtendAction

Spec ==
    Init /\ [][Next]_<<phase, ds, ss, primers, hybrids>> /\
    []NonNeg /\ []Conservation

LivenessCycles == []<>(phase = PhaseDenature)

LivenessProduction ==
    IF initPrimers > 0 /\ initSS > 0
    THEN <> (ds > initDS)
    ELSE TRUE

SpecWithLiveness ==
    Spec /\ LivenessCycles /\ LivenessProduction

THEOREM PCR_Complete == SpecWithLiveness