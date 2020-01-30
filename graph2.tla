------------------------------- MODULE graph2 -------------------------------
EXTENDS FiniteSets, Sequences, Integers
CONSTANTS Nodes, Succs
ASSUME Succs \in [Nodes -> SUBSET Nodes]
VARIABLE fun_stack, t_stack, num, col, sccs
RECURSIVE Path(_,_,_)

Edge(v, w) == w \in Succs[v]

Path(x, y, n) == IF n = 0 THEN x = y
                ELSE \E z \in Nodes : Path(x, z, n-1) /\ Edge(z, y)

Connected(x, y) == \E n \in 0..Cardinality(Nodes) : Path(x, y, n)

AllConnected(S) == \A x, y \in S : Connected(x, y) /\ Connected(y, x)

SCC(S) == /\ AllConnected(S)
            /\ \A T \in SUBSET Nodes :
                S \subseteq T /\ AllConnected(T) => S = T
                
 
                                     
dfs == /\ fun_stack /= <<>>
       /\ LET S == Head(fun_stack)
            IN /\ S \in SUBSET Nodes
               /\ \/ S = {} /\ fun_stack' = Tail(fun_stack)
                  \/ \E v \in S : LET t == S \ {v}
                                    IN /\ fun_stack' = <<v, t>> \o Tail(fun_stack)
                
dfs1 == \/ /\ fun_stack /= <<>>
           /\ LET v == Head(fun_stack)
                IN /\ v \in Nodes
                \* Vérifier qu'il n'est pas encore traité (couleur -> blanc) 
                   \* Si en cours de traitement (gris) -> un scc
                   /\ t_stack' = <<v>> \o t_stack  \* t devient en cours de traitement (gris)
                   /\ LET S == {w \in Nodes : Edge(v,w)} 
                        IN \/ S = {} /\ t_stack' = Tail(t_stack) \* Traitement -> noir
                           \/ fun_stack' = <<S>> \o Tail(fun_stack)
                   
       \/ /\ LET v == Head(t_stack)
                IN \* Traitement -> noir
                    /\ t_stack' = Tail(t_stack)
                   
          
Init == /\ sccs = {}
        /\ fun_stack = <<Nodes>>
       
        
Next == \/ dfs
        \/ dfs1

                                    
TypeOK == /\ fun_stack \in Seq(Nodes \union SUBSET Nodes)
        /\ t_stack \in Seq(Nodes)
        /\ num \in [Nodes -> Nat \union {-1}]
        /\ col \in [Nodes -> {"white", "gray", "black"}]
        /\ sccs \in SUBSET(SUBSET Nodes)

=============================================================================
\* Modification History
\* Last modified Thu Jan 30 16:44:50 CET 2020 by ipseiz5u
\* Last modified Thu Jan 30 14:12:11 CET 2020 by ipseiz5u
\* Last modified Sun Jan 26 13:52:03 CET 2020 by matth_000
\* Created Sun Jan 26 13:27:52 CET 2020 by matth_000
