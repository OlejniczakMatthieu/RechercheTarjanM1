---- MODULE MC ----
EXTENDS Tarjan, TLC

\* CONSTANT definitions @modelParameterConstants:0Succs
const_1587648743117163000 == 
(0 :> {}) @@
(1 :> {0,2,5,8}) @@
(2 :> {3}) @@
(3 :> {1,4}) @@
(4 :> {2}) @@
(5 :> {6}) @@
(6 :> {7}) @@
(7 :> {5}) @@
(8 :> {7,9}) @@
(9 :> {4})
----

\* CONSTANT definitions @modelParameterConstants:2Nodes
const_1587648743117164000 == 
0 .. 9
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1587648743117165000 ==
TLCConnected
----
=============================================================================
\* Modification History
\* Created Thu Apr 23 15:32:23 CEST 2020 by merz
