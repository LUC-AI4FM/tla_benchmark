------------------------------ MODULE ParamInstanceTest ------------------------------
(***************************************************************************)
(* A small test specification for parametrized INSTANCE usage.            *)
(* It is not meant to model an algorithm. It tests how a parametrized      *)
(* instance (ISpec) is handled compared with an instance that has an      *)
(* explicit substitution (JSpec).                                          *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE y

    ---------------------------- MODULE Inner ----------------------------
    EXTENDS Naturals
    VARIABLE x

    InnerInit == x = 0
    InnerNext == x' = (x + 1) % 5
    Spec      == InnerInit /\ [][InnerNext]_x
    ======================================================================