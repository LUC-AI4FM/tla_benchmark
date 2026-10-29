------------------------------- MODULE MC -------------------------------
(***************************************************************************)
(* Model-checking configuration module for the SPA_Attack_New spec.       *)
(* Following TLC's generated MC.tla convention, it gives concrete values  *)
(* for the network parameters through const_XXX definitions, which are    *)
(* substituted for the constants in the .cfg file. For example:           *)
(*     CONSTANT SPA_Server_IP <- const_SPA_Server_IP                       *)
(*                                                                         *)
(* So that SANY can parse this module on its own, it extends only         *)
(* standard modules and declares the parameters it configures. When used  *)
(* with the real model, replace the EXTENDS line with:                    *)
(*     EXTENDS SPA_Attack_New, TLC                                         *)
(* and delete the local CONSTANTS and the placeholder behavior below.     *)
(*                                                                         *)
(* This module has no variables, actions, temporal properties, or         *)
(* proofs. Init, Next and Spec are trivial placeholders.                  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    SPA_Server_IP,        \* IP address of the SPA-protected server
    SPA_Server_Port,      \* port on which the SPA daemon listens
    Protected_Port,       \* service port hidden behind SPA
    Client_IP,            \* IP address of the legitimate client
    Client_Port,          \* source port used by the legitimate client
    Client_ID,            \* identifier of the legitimate client
    Attacker_IP,          \* IP address of the attacker
    Attacker_Port,        \* source port used by the attacker
    Attacker_ID,          \* identifier of the attacker
    SYN_Flag,             \* TCP SYN flag
    ACK_Flag,             \* TCP ACK flag
    RST_Flag,             \* TCP RST flag
    FIN_Flag              \* TCP FIN flag

---------------------------------------------------------------------------
(* Concrete constant values supplied to the model                         *)
---------------------------------------------------------------------------

const_SPA_Server_IP   == "10.0.0.1"
const_SPA_Server_Port == 62201
const_Protected_Port  == 22

const_Client_IP       == "10.0.0.2"
const_Client_Port     == 40000
const_Client_ID       == "client1"

const_Attacker_IP     == "10.0.0.66"
const_Attacker_Port   == 50000
const_Attacker_ID     == "attacker1"

const_SYN_Flag        == "SYN"
const_ACK_Flag        == "ACK"
const_RST_Flag        == "RST"
const_FIN_Flag        == "FIN"

---------------------------------------------------------------------------
(* Sanity checks on the configured values                                  *)
---------------------------------------------------------------------------

const_IPs   == {const_SPA_Server_IP, const_Client_IP, const_Attacker_IP}
const_Ports == {const_SPA_Server_Port, const_Protected_Port,
                const_Client_Port, const_Attacker_Port}
const_Flags == {const_SYN_Flag, const_ACK_Flag, const_RST_Flag, const_FIN_Flag}

ConfigOK ==
    /\ Cardinality(const_IPs) = 3              \* all hosts are distinct
    /\ const_Ports \subseteq 0..65535          \* ports are valid
    /\ Cardinality(const_Flags) = 4            \* flags are distinct
    /\ const_Client_ID # const_Attacker_ID     \* identities are distinct

ASSUME ConfigOK

---------------------------------------------------------------------------
(* Placeholder behavior. MC defines no state; the real Init/Next/Spec     *)
(* come from SPA_Attack_New.                                               *)
---------------------------------------------------------------------------

Init == TRUE

Next == TRUE

Spec == Init /\ [][Next]_<<>>

Invariant == ConfigOK

=============================================================================