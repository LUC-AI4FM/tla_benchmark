------------------------------- MODULE MC -------------------------------
(***************************************************************************)
(* Model-checking parameterization module for the SPA (Single Packet      *)
(* Authorization) attack model SPA_Attack_New.  This module only supplies  *)
(* concrete values for the network configuration constants: IP addresses, *)
(* ports, TCP flags, and identifiers for the attacker and client.          *)
(*                                                                         *)
(* It defines no protocol behavior.  So that the module can be parsed and  *)
(* model-checked on its own, it holds the chosen configuration in a single *)
(* variable that never changes.                                            *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    MaxPort          \* upper bound on valid port numbers (e.g. 65535)

VARIABLES
    config           \* the frozen model configuration record

vars == << config >>

(***************************************************************************)
(* Concrete constant values (in the style of TLC-generated MC definitions).*)
(***************************************************************************)

\* IP addresses (encoded as strings)
const_ServerIP    == "10.0.0.1"
const_ClientIP    == "10.0.0.2"
const_AttackerIP  == "10.0.0.66"
const_SpoofedIP   == "10.0.0.2"       \* attacker spoofs the client's address

\* Ports
const_SPAPort         == 62201          \* UDP port where the SPA daemon listens
const_ProtectedPort   == 22             \* service hidden behind SPA (e.g. SSH)
const_ClientSrcPort   == 40000
const_AttackerSrcPort == 50000

\* TCP flags
const_SYN    == "SYN"
const_ACK    == "ACK"
const_SYNACK == "SYN_ACK"
const_RST    == "RST"
const_FIN    == "FIN"
const_Flags  == { const_SYN, const_ACK, const_SYNACK, const_RST, const_FIN }

\* Identifiers for the participants
const_ClientID   == "client"
const_AttackerID == "attacker"
const_ServerID   == "server"
const_Agents     == { const_ClientID, const_AttackerID, const_ServerID }

\* Attacker and client configuration records
const_ClientConfig ==
    [ id      |-> const_ClientID,
      ip      |-> const_ClientIP,
      srcPort |-> const_ClientSrcPort,
      dstPort |-> const_ProtectedPort,
      hasKey  |-> TRUE ]

const_AttackerConfig ==
    [ id        |-> const_AttackerID,
      ip        |-> const_AttackerIP,
      spoofIP   |-> const_SpoofedIP,
      srcPort   |-> const_AttackerSrcPort,
      dstPort   |-> const_ProtectedPort,
      hasKey    |-> FALSE,
      canSniff  |-> TRUE,
      canReplay |-> TRUE ]

const_ServerConfig ==
    [ id            |-> const_ServerID,
      ip            |-> const_ServerIP,
      spaPort       |-> const_SPAPort,
      protectedPort |-> const_ProtectedPort ]

\* Complete model configuration
const_Config ==
    [ client   |-> const_ClientConfig,
      attacker |-> const_AttackerConfig,
      server   |-> const_ServerConfig,
      flags    |-> const_Flags ]

(***************************************************************************)
(* Well-formedness of the configuration                                    *)
(***************************************************************************)
ValidPort(p) == p \in 1..MaxPort

ConfigWellFormed ==
    /\ ValidPort(config.client.srcPort)
    /\ ValidPort(config.client.dstPort)
    /\ ValidPort(config.attacker.srcPort)
    /\ ValidPort(config.attacker.dstPort)
    /\ ValidPort(config.server.spaPort)
    /\ ValidPort(config.server.protectedPort)
    /\ config.server.spaPort # config.server.protectedPort
    /\ config.client.id # config.attacker.id
    /\ config.attacker.ip # config.client.ip
    /\ config.client.hasKey = TRUE
    /\ config.attacker.hasKey = FALSE
    /\ config.flags = const_Flags

(***************************************************************************)
(* Specification: the configuration is fixed and never changes             *)
(***************************************************************************)
Init == config = const_Config

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ config.flags \subseteq const_Flags
    /\ config.client.id \in const_Agents
    /\ config.attacker.id \in const_Agents
    /\ config.server.id \in const_Agents

ConfigConstant == [][config' = config]_vars

THEOREM Spec => [](TypeOK /\ ConfigWellFormed)
=============================================================================