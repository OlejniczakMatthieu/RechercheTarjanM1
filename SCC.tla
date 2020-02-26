-------------------------------- MODULE SCC --------------------------------
(***************************************************************************)
(* This module contains mathematical definitions about graphs, and in      *)
(* particular the notion of strongly connected components.                 *)
(***************************************************************************)

CONSTANTS Nodes, Succs
ASSUME SuccsType == Succs \in [Nodes -> SUBSET Nodes]

(***************************************************************************)
(* We have defined the graph by the set of nodes and "successor lists":    *)
(* the function Succs returns the set of successors of any given node.     *)
(* Equivalently, we could have used the set of edges, computed as follows. *)
(***************************************************************************)
Edges ==
  LET E(n) == { <<n,m>> : m \in Succs[n] }
  IN  UNION {E(n) : n \in Nodes}
  
(***************************************************************************)
(* For notions about paths in graphs, we need the reflexive and transitive *)
(* closure of the edge relation, which we define recursively as follows.   *)
(* For efficient evaluation, our definition follows Warshall's algorithm.  *)
(***************************************************************************)
Connected ==
  LET TE[N \in SUBSET Nodes] ==
        IF N = {} THEN Edges \cup {<<n,n>> : n \in Nodes}
        ELSE LET n == CHOOSE n \in N : TRUE
                 TER == TE[N \ {n}]
             IN  TER \cup { e \in Nodes \X Nodes :
                            <<e[1],n>> \in TER /\ <<n,e[2]>> \in TER }
  IN  TE[Nodes]

(***************************************************************************)
(* A set (of nodes) is fully connected if its nodes are pairwise connected *)
(* to each other.                                                          *)
(***************************************************************************)
FullyConnected(S) == 
  \A x, y \in S : <<x,y>> \in Connected /\ <<y,x>> \in Connected

(***************************************************************************)
(* A set (of nodes) is an SCC if it is fully connected and maximal.        *)
(***************************************************************************)
SCC(S) == 
  /\ FullyConnected(S)
  /\ \A T \in SUBSET Nodes : S \subseteq T /\ FullyConnected(T) => S = T

(***************************************************************************)
(* The following definition computes the set of all SCCs of the graph.     *)
(***************************************************************************)
SCCs == { S \in SUBSET Nodes : SCC(S) }

=============================================================================
\* Modification History
\* Last modified Thu Feb 20 18:11:47 CET 2020 by merz
\* Created Thu Feb 20 15:38:49 CET 2020 by merz
