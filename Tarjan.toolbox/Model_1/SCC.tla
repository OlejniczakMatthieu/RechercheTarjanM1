-------------------------------- MODULE SCC ---------------------------------
(***************************************************************************)
(* This module contains mathematical definitions about graphs, and in      *)
(* particular the notion of strongly connected components.                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS Nodes, Succs
ASSUME SuccsType == Succs \in [Nodes -> SUBSET Nodes]
USE SuccsType

(***************************************************************************)
(* We have defined the graph by the set of nodes and "successor lists":    *)
(* the function Succs returns the set of successors of any given node.     *)
(* Equivalently, we could have used the set of edges, computed as follows. *)
(***************************************************************************)
Edges ==
  LET E(n) == { <<n,m>> : m \in Succs[n] }
  IN  UNION {E(n) : n \in Nodes}

LEMMA EdgeLemma == \A m,n \in Nodes : <<m,n>> \in Edges <=> n \in Succs[m]
BY DEF Edges
  
(***************************************************************************)
(* For notions about paths in graphs, we need the reflexive and transitive *)
(* closure of the edge relation. We give two definitions below: one using  *)
(* explicit paths in the graph and a recursive definition inspired by      *)
(* Warshall's algorithm, which can be evaluated quite efficiently by TLC.  *)
(* When model checking, override the operator Connected by TLCConnected.   *)
(***************************************************************************)
Path(m,n) == \E p \in Seq(Nodes) \ {<< >>} :
  /\ p[1] = m
  /\ p[Len(p)] = n
  /\ \A i \in 1 .. Len(p)-1 : p[i+1] \in Succs[p[i]]
  
Connected == { mn \in Nodes \X Nodes : Path(mn[1], mn[2]) }

TLCConnected ==
  LET TE[N \in SUBSET Nodes] ==
        IF N = {} THEN Edges \cup {<<n,n>> : n \in Nodes}
        ELSE LET n == CHOOSE n \in N : TRUE
                 TER == TE[N \ {n}]
             IN  TER \cup { e \in Nodes \X Nodes :
                            <<e[1],n>> \in TER /\ <<n,e[2]>> \in TER }
  IN  TE[Nodes]

LEMMA ConnectedReflexive == 
  ASSUME NEW n \in Nodes
  PROVE  <<n,n>> \in Connected
<1>. /\ <<n>> \in Seq(Nodes) \ {<<>>}
     /\ Path(n,n)!(<<n>>)
  OBVIOUS
<1>. QED  BY Zenon DEF Connected, Path

LEMMA SuccsConnected ==
  ASSUME NEW m \in Nodes, NEW n \in Succs[m]
  PROVE  <<m,n>> \in Connected
<1>. /\ <<m,n>> \in Seq(Nodes) \ {<<>>}
     /\ Path(m,n)!(<<m,n>>)
  OBVIOUS
<1>. QED  BY Zenon DEF Connected, Path

LEMMA ConnectedTransitive ==
  ASSUME NEW x \in Nodes, NEW y \in Nodes, NEW z \in Nodes,
         <<x,y>> \in Connected, <<y,z>> \in Connected
  PROVE  <<x,z>> \in Connected
<1>1. PICK p1 \in Seq(Nodes) \ {<<>>} : Path(x,y)!(p1)
  BY DEF Connected, Path
<1>2. PICK p2 \in Seq(Nodes) \ {<<>>} : Path(y,z)!(p2)
  BY DEF Connected, Path
<1>. DEFINE p == p1 \o Tail(p2)
<1>3. /\ p \in Seq(Nodes) \ {<<>>}
      /\ Path(x,z)!(p)
  BY <1>1, <1>2
<1>. QED  BY <1>3, Zenon DEF Connected, Path

(***************************************************************************)
(* A path that leads from a node in some set S to some node outside S      *)
(* contains a transition from some node in S to a node outside S.          *)
(***************************************************************************)
LEMMA ReachableCrossingSet ==
  ASSUME NEW S \in SUBSET Nodes, NEW x \in S, NEW y \in Nodes \ S,
         <<x,y>> \in Connected
  PROVE  \E m,n \in Nodes : /\ m \in S /\ n \notin S
                            /\ n \in Succs[m]
                            /\ <<x,m>> \in Connected
                            /\ <<n,y>> \in Connected
<1>1. PICK p \in Seq(Nodes) \ {<< >>} : 
             /\ p[1] = x
             /\ p[Len(p)] = y
             /\ \A i \in 1 .. Len(p)-1 : p[i+1] \in Succs[p[i]]
  BY DEF Connected, Path
<1>. DEFINE NonS == { i \in 1 .. Len(p) : p[i] \notin S }
<1>2. NonS \in SUBSET Nat /\ NonS # {} /\ 1 \notin NonS
  BY <1>1
<1>3. PICK i \in 1 .. Len(p) :
             /\ i \in NonS
             /\ \A j \in 0 .. i-1 : j \notin NonS
  <2>. DEFINE P(n) == n \in NonS
  <2>1. PICK n \in Nat : P(n)  BY <1>2
  <2>. HIDE DEF P
  <2>2. PICK i \in Nat : P(i) /\ \A j \in 0 .. i-1 : ~P(j)
    BY <2>1, SmallestNatural, Isa
  <2>. QED  BY <2>2 DEF P
<1>. DEFINE m == p[i-1]
            n == p[i]
<1>4. i > 1 /\ m \in Nodes /\ n \in Nodes /\ m \in S /\ n \notin S /\ n \in Succs[m]
  BY <1>1, <1>2, <1>3
<1>5. <<x,m>> \in Connected
  <2>. DEFINE xm == SubSeq(p,1,i-1)
  <2>1. /\ xm \in Seq(Nodes) \ {<<>>}
        /\ Path(x,m)!(xm)
    BY <1>1, <1>2, <1>3, <1>4, SubSeqProperties, Z3T(30)
  <2>. HIDE DEF xm, m
  <2>. QED  BY <2>1, <1>4 DEF Connected, Path
<1>6. <<n,y>> \in Connected
  <2>. DEFINE ny == SubSeq(p,i,Len(p))
  <2>1. /\ ny \in Seq(Nodes) \ {<<>>}
        /\ Path(n,y)!(ny)
    BY <1>1, <1>2, <1>3, <1>4, SubSeqProperties, Z3T(30)
  <2>. HIDE DEF ny, n
  <2>. QED  BY <2>1, <1>4 DEF Connected, Path
<1>. QED  BY <1>4, <1>5, <1>6, Zenon

(***************************************************************************)
(* A set (of nodes) is fully connected if its nodes are pairwise connected *)
(* to each other.                                                          *)
(***************************************************************************)
FullyConnected(S) == 
  \A x, y \in S : <<x,y>> \in Connected /\ <<y,x>> \in Connected

LEMMA FullyConnectedAdd ==
  ASSUME NEW S \in SUBSET Nodes, FullyConnected(S),
         NEW x \in S, NEW y \in Nodes,
         <<x,y>> \in Connected, <<y,x>> \in Connected
  PROVE  FullyConnected(S \cup {y})
BY ConnectedTransitive, Zenon DEF FullyConnected

(***************************************************************************)
(* A set (of nodes) is an SCC if it is fully connected and maximal.        *)
(***************************************************************************)
SCC(S) == 
  /\ FullyConnected(S)
  /\ \A T \in SUBSET Nodes : S \subseteq T /\ FullyConnected(T) => S = T

(***************************************************************************)
(* If a node x belongs to an SCC and y is another node such that x and y   *)
(* are reachable from each other then y belongs to the same SCC as x.      *)
(***************************************************************************)
LEMMA MutuallyReachableSameSCC ==
  ASSUME NEW S \in SUBSET Nodes, SCC(S),
         NEW x \in S, NEW y \in Nodes,
         <<x,y>> \in Connected, <<y,x>> \in Connected
  PROVE  y \in S
<1>1. FullyConnected(S \cup {y})
  BY FullyConnectedAdd DEF SCC
<1>. QED  BY <1>1 DEF SCC

(***************************************************************************)
(* Two SCCs that intersect are identical.                                  *)
(***************************************************************************)
LEMMA SCCPartition ==
  ASSUME NEW S \in SUBSET Nodes, SCC(S),
         NEW T \in SUBSET Nodes, SCC(T),
         S \cap T # {}
  PROVE  S = T
BY MutuallyReachableSameSCC, Zenon DEF SCC, FullyConnected

(***************************************************************************)
(* The following definition computes the set of all SCCs of the graph.     *)
(***************************************************************************)
SCCs == { S \in SUBSET Nodes : SCC(S) }

=============================================================================
\* Modification History
\* Last modified Mon Mar 02 17:59:57 CET 2020 by merz
\* Created Thu Feb 20 15:38:49 CET 2020 by merz
