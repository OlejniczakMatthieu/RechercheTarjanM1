------------------------------- MODULE graph2 -------------------------------
EXTENDS FiniteSets, Sequences, Integers
CONSTANTS Nodes, Succs
ASSUME Succs \in [Nodes -> SUBSET Nodes]
VARIABLE fun_stack, t_stack, num, lowlink, col, i,sccs
RECURSIVE Path(_,_,_)

INFTY == Cardinality(Nodes)+1

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
            IN /\ S.kind = "dfs"
               /\ S.arg \in SUBSET Nodes
               /\ \/ S.arg = {} /\ fun_stack' = Tail(fun_stack)
                  \/ \E x \in S.arg : LET t == S.arg \ {x}
                                    IN IF num[x] /= -1
                                        THEN  LET r == [kind |-> "dfs1b", arg |-> t, res |-> num[x]]
                                              IN fun_stack' = <<r, t>> \o Tail(fun_stack)                                         
                                        ELSE
                                              LET r == [kind |-> "dfs1", arg |-> x, res |-> num[x]]
                                              IN fun_stack' = <<r, t>> \o Tail(fun_stack)

(**dfsb == /\ LET S == Head(fun_stack)
           IN  /\ S.kind == "dfsb"
               /\ n1 == S.res
               /\ LET t == S.arg
                   IN /\ r == [kind |-> "dfs", arg, res] 
                   
**)                    
        
        
(**                
dfs1 == \/ /\ fun_stack /= <<>> 
           /\ LET v == Head(fun_stack)
                IN /\ v \in Nodes
                    \* Vérifier qu'il n'est pas encore traité (couleur -> blanc) 
                   /\ IF col[v] = "white" 
                      THEN  /\ t_stack' = <<v>> \o t_stack 
                             \* v devient en cours de traitement (gris)
                            /\ col'= [col EXCEPT ![v] = "gray"]
                            /\ num' = [num EXCEPT ![v] = i]
                            /\ lowlink' = [lowlink EXCEPT ![v] = num[v]]
                            /\ i' = i + 1
                            /\ LET S == {w \in Nodes : Edge(v,w)} 
                                IN \/ S = {} /\ t_stack' = Tail(t_stack) 
                                   \/ fun_stack' = <<S>> \o Tail(fun_stack)                   
                      ELSE fun_stack' = fun_stack
       \/  LET v == Head(t_stack)
                IN \* Traitement -> noir
                    /\ col' = [col EXCEPT ![v] = "black"]
                    /\ t_stack' = Tail(t_stack)
**)

dfs1 ==
  /\ LET r == Head(fun_stack)
         newr == [r EXCEPT !.kind = "dfs1b"]
     IN  /\ r.kind = "dfs1"
         /\ fun_stack' = <<[kind |-> "dfs", arg |-> Succs[r.arg], res |-> -1],
                            newr>>
                          \o Tail(fun_stack)
         /\ t_stack' = <<r.arg>> \o t_stack
         /\ i' = i+1
         /\ num' = [num EXCEPT ![r.arg] = i]
         /\ UNCHANGED <<col, sccs>>

dfs1b ==
  /\ LET r == Head(fun_stack)
         below == Head(Tail(fun_stack))
     IN  /\ r.kind = "dfs1b"
         /\ IF r.res < num[r.arg]
            THEN /\ fun_stack' = <<[below EXCEPT !.res = r.res]>> \o Tail(Tail(fun_stack))
                 /\ UNCHANGED <<t_stack,i,num,col,sccs>>
            ELSE LET n == CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = r.arg
                     scc == {t_stack[k] : k \in 1 .. n}
                 IN  /\ t_stack' = SubSeq(t_stack, n+1, Len(t_stack))
                     /\ sccs' = sccs \cup {scc}
                     /\ num' = [x \in Nodes |-> IF x \in scc THEN INFTY ELSE num[x]]
                     /\ fun_stack' = <<[below EXCEPT !.res = INFTY]>> \o Tail(Tail(fun_stack))
          
Init == /\ sccs = {}
        /\ fun_stack = [kind |-> "dfs", arg |-> <<Nodes>>, res |-> -1]
        /\ num = [n \in Nodes |-> -1]
        /\ lowlink = [n \in Nodes |-> -1] 
        /\ col = [n \in Nodes |-> "white"]
        /\ i = 0
       
        
Next == \/ dfs
        \/ dfs1

                                    
TypeOK == /\ fun_stack \in Seq(Nodes \union SUBSET Nodes)
          /\ t_stack \in Seq(Nodes)
          /\ num \in [Nodes -> Nat \union {-1}]
          /\ lowlink \in [Nodes -> Nat \union {-1}]
          /\ col \in [Nodes -> {"white", "gray", "black"}]
          /\ sccs \in SUBSET(SUBSET Nodes)

=============================================================================
