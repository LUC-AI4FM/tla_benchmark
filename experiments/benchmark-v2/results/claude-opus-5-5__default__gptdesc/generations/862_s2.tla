---------------------------- MODULE MC ----------------------------
EXTENDS SPA_Attack_New, TLC

\* Model parameters for model checking SPA_Attack_New.
\* Each definition below overrides a CONSTANT of the extended module
\* (see the CONSTANT section of MC.cfg).

\* CONSTANT definitions @modelParameterConstants:0ServerIP
const_ServerIP ==
"10.0.0.1"
----

\* CONSTANT definitions @modelParameterConstants:1ClientIP
const_ClientIP ==
"10.0.0.2"
----

\* CONSTANT definitions @modelParameterConstants:2AttackerIP
const_AttackerIP ==
"10.0.0.66"
----

\* CONSTANT definitions @modelParameterConstants:3SPAPort
const_SPAPort ==
62201
----

\* CONSTANT definitions @modelParameterConstants:4ServicePort
const_ServicePort ==
22
----

\* CONSTANT definitions @modelParameterConstants:5ClientSrcPort
const_ClientSrcPort ==
40000
----

\* CONSTANT definitions @modelParameterConstants:6AttackerSrcPort
const_AttackerSrcPort ==
50000
----

\* CONSTANT definitions @modelParameterConstants:7SYN
const_SYN ==
"SYN"
----

\* CONSTANT definitions @modelParameterConstants:8ACK
const_ACK ==
"ACK"
----

\* CONSTANT definitions @modelParameterConstants:9SYNACK
const_SYNACK ==
"SYNACK"
----

\* CONSTANT definitions @modelParameterConstants:10RST
const_RST ==
"RST"
----

\* CONSTANT definitions @modelParameterConstants:11ClientID
const_ClientID ==
"client"
----

\* CONSTANT definitions @modelParameterConstants:12AttackerID
const_AttackerID ==
"attacker"
----

\* CONSTANT definitions @modelParameterConstants:13ServerID
const_ServerID ==
"server"
----

\* CONSTANT definitions @modelParameterConstants:14Flags
const_Flags ==
{"SYN", "ACK", "SYNACK", "RST"}
----

\* CONSTANT definitions @modelParameterConstants:15Agents
const_Agents ==
{"client", "attacker", "server"}
----

\* CONSTANT definitions @modelParameterConstants:16MaxSeq
const_MaxSeq ==
3
----

=============================================================================