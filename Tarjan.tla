------------------------------- MODULE Tarjan -------------------------------
EXTENDS FiniteSets, Sequences, Integers, SCC, TLAPS, FiniteSetTheorems

ASSUME NodesFinite == IsFiniteSet(Nodes)
(***************************************************************************)
(* The algorithm in pseudo-code (from Wikipedia):                          *)
(*                                                                         *)
(* algorithm tarjan is                                                     *)
(*     input: graph G = (V, E)                                             *)
(*     output: set of strongly connected components (sets of vertices)     *)
(*                                                                         *)
(*     index := 0                                                          *)
(*     S := empty stack                                                    *)
(*     for each v in V do                                                  *)
(*         if v.index is undefined then                                    *)
(*             strongconnect(v)                                            *)
(*         end if                                                          *)
(*     end for                                                             *)
(*                                                                         *)
(*     function strongconnect(v)                                           *)
(*         // Set the depth index for v to the smallest unused index       *)
(*         v.index := index                                                *)
(*         v.lowlink := index                                              *)
(*         index := index + 1                                              *)
(*         S.push(v)                                                       *)
(*         v.onStack := true                                               *)
(*                                                                         *)
(*         // Consider successors of v                                     *)
(*         for each (v, w) in E do                                         *)
(*             if w.index is undefined then                                *)
(*                 // Successor w has not yet been visited; recurse on it  *)
(*                 strongconnect(w)                                        *)
(*                 v.lowlink := min(v.lowlink, w.lowlink)                  *)
(*             else if w.onStack then                                      *)
(*                 // Successor w is in stack S and hence in the current SCC *)
(*                 // If w is not on stack, then (v, w) is a cross-edge in the DFS tree and must be ignored *)
(*                 // Note: The next line may look odd - but is correct.   *)
(*                 // It says w.index not w.lowlink; that is deliberate and from the original paper *)
(*                 v.lowlink := min(v.lowlink, w.index)                    *)
(*             end if                                                      *)
(*         end for                                                         *)
(*                                                                         *)
(*         // If v is a root node, pop the stack and generate an SCC       *)
(*         if v.lowlink = v.index then                                     *)
(*             start a new strongly connected component                    *)
(*             repeat                                                      *)
(*                 w := S.pop()                                            *)
(*                 w.onStack := false                                      *)
(*                 add w to current strongly connected component           *)
(*             while w ≠ v                                                 *)
(*             output the current strongly connected component             *)
(*         end if                                                          *)
(*     end function                                                        *)
(*                                                                         *)
(* We rewrite this algorithm in PlusCal, an algorithm language that has a  *)
(* translator for generating a TLA+ specification.                         *)
(***************************************************************************)

(*--algorithm Tarjan {
  variables 
    index = 0, 
    t_stack = << >>, 
    num = [n \in Nodes |-> -1], 
    lowlink = [n \in Nodes |-> -1], 
    onStack = [n \in Nodes |-> FALSE], 
    sccs = {},
    toVisit = Nodes;

  procedure visit(v) 
    variable succs = {}, w; 
  {
start_visit:
    num[v] := index;
    lowlink[v] := index;
    index := index+1;
    t_stack := <<v>> \o t_stack;
    onStack[v] := TRUE;
    succs := Succs[v];

explore_succ:    
    while (succs # {}) {
      with (s \in succs) { w := s; succs := succs \ {s} };
      if (num[w] = -1) {
visit_recurse:
        call visit(w);
continue_visit:
        if (lowlink[w] < lowlink[v]) { lowlink[v] := lowlink[w] }
      } else if (onStack[w]) {
        if (num[w] < lowlink[v]) { lowlink[v] := num[w] }
      }
    };
check_root:
    if (lowlink[v] = num[v] /\ (\E k \in 1 .. Len(t_stack) : t_stack[k] = v)) {
      \* new SCC found: pop all nodes up to v from the (Tarjan) stack
      with (k = CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = v) {
        sccs := sccs \cup {{t_stack[i] : i \in 1 .. k}};
        onStack := [n \in Nodes |-> IF \E i \in 1 .. k : n = t_stack[i] THEN FALSE
                                    ELSE onStack[n]];
        t_stack := SubSeq(t_stack, k+1, Len(t_stack))
      }
    };
    return;
  }
  
  { \* body of main algorithm
main:
    while (toVisit # {}) {
      with (n \in toVisit) {
        toVisit := toVisit \ {n};
        if (num[n] = -1) { call visit(n) }
      }
    }
  }
}
*)
\* BEGIN TRANSLATION PCal-0b7e38f16f0a4b3ff74373336ba37ec3
CONSTANT defaultInitValue
VARIABLES index, t_stack, num, lowlink, onStack, sccs, toVisit, pc, stack, v, 
          succs, w

vars == << index, t_stack, num, lowlink, onStack, sccs, toVisit, pc, stack, v, 
           succs, w >>

Init == (* Global variables *)
        /\ index = 0
        /\ t_stack = << >>
        /\ num = [n \in Nodes |-> -1]
        /\ lowlink = [n \in Nodes |-> -1]
        /\ onStack = [n \in Nodes |-> FALSE]
        /\ sccs = {}
        /\ toVisit = Nodes
        (* Procedure visit *)
        /\ v = defaultInitValue
        /\ succs = {}
        /\ w = defaultInitValue
        /\ stack = << >>
        /\ pc = "main"

start_visit == /\ pc = "start_visit"
               /\ num' = [num EXCEPT ![v] = index]
               /\ lowlink' = [lowlink EXCEPT ![v] = index]
               /\ index' = index+1
               /\ t_stack' = <<v>> \o t_stack
               /\ onStack' = [onStack EXCEPT ![v] = TRUE]
               /\ succs' = Succs[v]
               /\ pc' = "explore_succ"
               /\ UNCHANGED << sccs, toVisit, stack, v, w >>

explore_succ == /\ pc = "explore_succ"
                /\ IF succs # {}
                      THEN /\ \E s \in succs:
                                /\ w' = s
                                /\ succs' = succs \ {s}
                           /\ IF num[w'] = -1
                                 THEN /\ pc' = "visit_recurse"
                                      /\ UNCHANGED lowlink
                                 ELSE /\ IF onStack[w']
                                            THEN /\ IF num[w'] < lowlink[v]
                                                       THEN /\ lowlink' = [lowlink EXCEPT ![v] = num[w']]
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED lowlink
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED lowlink
                                      /\ pc' = "explore_succ"
                      ELSE /\ pc' = "check_root"
                           /\ UNCHANGED << lowlink, succs, w >>
                /\ UNCHANGED << index, t_stack, num, onStack, sccs, toVisit, 
                                stack, v >>

visit_recurse == /\ pc = "visit_recurse"
                 /\ /\ stack' = << [ procedure |->  "visit",
                                     pc        |->  "continue_visit",
                                     succs     |->  succs,
                                     w         |->  w,
                                     v         |->  v ] >>
                                 \o stack
                    /\ v' = w
                 /\ succs' = {}
                 /\ w' = defaultInitValue
                 /\ pc' = "start_visit"
                 /\ UNCHANGED << index, t_stack, num, lowlink, onStack, sccs, 
                                 toVisit >>

continue_visit == /\ pc = "continue_visit"
                  /\ IF lowlink[w] < lowlink[v]
                        THEN /\ lowlink' = [lowlink EXCEPT ![v] = lowlink[w]]
                        ELSE /\ TRUE
                             /\ UNCHANGED lowlink
                  /\ pc' = "explore_succ"
                  /\ UNCHANGED << index, t_stack, num, onStack, sccs, toVisit, 
                                  stack, v, succs, w >>

check_root == /\ pc = "check_root"
              /\ IF lowlink[v] = num[v] /\ (\E k \in 1 .. Len(t_stack) : t_stack[k] = v)
                    THEN /\ LET k == CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = v IN
                              /\ sccs' = (sccs \cup {{t_stack[i] : i \in 1 .. k}})
                              /\ onStack' = [n \in Nodes |-> IF \E i \in 1 .. k : n = t_stack[i] THEN FALSE
                                                             ELSE onStack[n]]
                              /\ t_stack' = SubSeq(t_stack, k+1, Len(t_stack))
                    ELSE /\ TRUE
                         /\ UNCHANGED << t_stack, onStack, sccs >>
              /\ pc' = Head(stack).pc
              /\ succs' = Head(stack).succs
              /\ w' = Head(stack).w
              /\ v' = Head(stack).v
              /\ stack' = Tail(stack)
              /\ UNCHANGED << index, num, lowlink, toVisit >>

visit == start_visit \/ explore_succ \/ visit_recurse \/ continue_visit
            \/ check_root

main == /\ pc = "main"
        /\ IF toVisit # {}
              THEN /\ \E n \in toVisit:
                        /\ toVisit' = toVisit \ {n}
                        /\ IF num[n] = -1
                              THEN /\ /\ stack' = << [ procedure |->  "visit",
                                                       pc        |->  "main",
                                                       succs     |->  succs,
                                                       w         |->  w,
                                                       v         |->  v ] >>
                                                   \o stack
                                      /\ v' = n
                                   /\ succs' = {}
                                   /\ w' = defaultInitValue
                                   /\ pc' = "start_visit"
                              ELSE /\ pc' = "main"
                                   /\ UNCHANGED << stack, v, succs, w >>
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << toVisit, stack, v, succs, w >>
        /\ UNCHANGED << index, t_stack, num, lowlink, onStack, sccs >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == visit \/ main
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION TLA-ca633d7928a0211fc004f869a2523ede

ASSUME defaultNotNode == defaultInitValue \notin Nodes
USE defaultNotNode

Correct == pc = "Done" => sccs = SCCs

StackEntry == [
   procedure : {"visit"},
   pc : {"continue_visit", "main"},
   succs : SUBSET Nodes,
   w : Nodes \cup {defaultInitValue},
   v : Nodes \cup {defaultInitValue}
]

TypeOK ==
  /\ index \in Nat
  /\ t_stack \in Seq(Nodes)
  /\ num \in [Nodes -> Nat \cup {-1}]
  /\ lowlink \in [Nodes -> Nat \cup {-1}]
  /\ onStack \in [Nodes -> BOOLEAN]
  /\ sccs \in SUBSET SUBSET Nodes
  /\ toVisit \in SUBSET Nodes
  /\ pc \in {"main", "Done", "start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"}
  /\ stack \in Seq(StackEntry)
  /\ \A i \in 1 .. Len(stack) :
        \/ /\ i < Len(stack)
           /\ stack[i].pc = "continue_visit"
           /\ stack[i].v \in Nodes /\ num[stack[i].v] \in Nat
           /\ stack[i].succs \subseteq Succs[stack[i].v]
           /\ stack[i].w \in Nodes /\ stack[i].w \in Succs[stack[i].v]
        \/ /\ i = Len(stack)
           /\ stack[i].pc = "main"
           /\ stack[i].v = defaultInitValue
  /\ \/ pc \in {"main", "Done"} /\ stack = << >>
     \/ /\ pc \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"}
        /\ stack # << >>
  /\ succs \in SUBSET Nodes
  /\ pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"} => succs \subseteq Succs[v]
  /\ pc = "check_root" => succs = {}
  /\ v \in Nodes \cup {defaultInitValue}
  /\ \/ pc \in {"main", "Done"} /\ v = defaultInitValue
     \/ /\ pc \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"}
        /\ v \in Nodes
  /\ pc = "start_visit" => num[v] = -1
  /\ pc = "visit_recurse" => num[w] = -1
  /\ pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"} => num[v] \in Nat
  /\ pc \in {"visit_recurse", "continue_visit"} => w \in Nodes /\ w \in Succs[v]
  /\ w \in Nodes \cup {defaultInitValue}

USE SuccsType
USE NodesFinite

THEOREM TypeCorrect == Spec => []TypeOK
<1>init. Init => TypeOK
  BY DEF Init, TypeOK
<1>next. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <2>. USE DEF TypeOK
  <2>1. CASE start_visit
    BY <2>1 DEF start_visit
  <2>2. CASE explore_succ
    BY <2>2 DEF explore_succ
  <2>3. CASE visit_recurse
    <3>1. (index \in Nat)'
      BY <2>3 DEF visit_recurse
    <3>2. (t_stack \in Seq(Nodes))'
      BY <2>3 DEF visit_recurse
    <3>3. (num \in [Nodes -> Nat \cup {-1}])'
      BY <2>3 DEF visit_recurse
    <3>4. (lowlink \in [Nodes -> Nat \cup {-1}])'
      BY <2>3 DEF visit_recurse
    <3>5. (onStack \in [Nodes -> BOOLEAN])'
      BY <2>3 DEF visit_recurse
    <3>6. (sccs \in SUBSET SUBSET Nodes)'
      BY <2>3 DEF visit_recurse
    <3>7. (toVisit \in SUBSET Nodes)'
      BY <2>3 DEF visit_recurse
    <3>8. (pc \in {"main", "Done", "start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"})'
      BY <2>3 DEF visit_recurse
    <3>9. (stack \in Seq(StackEntry))'
      BY <2>3 DEF visit_recurse, StackEntry
    <3>10. (\A i \in 1 .. Len(stack) :
               \/ /\ i < Len(stack)
                  /\ stack[i].pc = "continue_visit"
                  /\ stack[i].v \in Nodes /\ num[stack[i].v] \in Nat
                  /\ stack[i].succs \subseteq Succs[stack[i].v]
                  /\ stack[i].w \in Nodes /\ stack[i].w \in Succs[stack[i].v]
               \/ /\ i = Len(stack)
                  /\ stack[i].pc = "main"
                  /\ stack[i].v = defaultInitValue)'
      BY <2>3 DEF visit_recurse
    <3>11. (\/ pc \in {"main", "Done"} /\ stack = << >>
            \/ /\ pc \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"}
               /\ stack # << >>)'
      BY <2>3 DEF visit_recurse
    <3>12. (succs \in SUBSET Nodes)'
      BY <2>3 DEF visit_recurse
    <3>a. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"} => succs \subseteq Succs[v])'
      BY <2>3 DEF visit_recurse
    <3>13. (pc = "check_root" => succs = {})'
      BY <2>3 DEF visit_recurse
    <3>14. (v \in Nodes \cup {defaultInitValue})'
      BY <2>3 DEF visit_recurse
    <3>15. (\/ pc \in {"main", "Done"} /\ v = defaultInitValue
            \/ /\ pc \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"}
               /\ v \in Nodes)'
      BY <2>3 DEF visit_recurse
    <3>16. (pc = "start_visit" => num[v] = -1)'
       <4>1. v' = w
          BY <2>3 DEF visit_recurse
       <4>2. num[w] = -1
          BY <2>3 DEF visit_recurse 
       <4> QED BY <2>3, <4>1, <4>2 DEF StackEntry, visit_recurse
    <3>17. (pc = "visit_recurse" => num[w] = -1)'
      BY <2>3 DEF visit_recurse
    <3>18. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"} => num[v] \in Nat)'
      BY <2>3 DEF visit_recurse
    <3>19. (pc \in {"visit_recurse", "continue_visit"} => w \in Nodes /\ w \in Succs[v])'
      BY <2>3 DEF visit_recurse
    <3>20. (w \in Nodes \cup {defaultInitValue})'
      BY <2>3 DEF visit_recurse
    <3>. QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10,
           <3>11, <3>12, <3>a, <3>13, <3>14, <3>15, <3>16, <3>17, <3>18, <3>19, <3>20
  <2>4. CASE continue_visit
    BY <2>4 DEF continue_visit
  <2>5. CASE check_root
    <3>1. (index \in Nat)'
      BY <2>5 DEF check_root
    <3>2. (t_stack \in Seq(Nodes))'
      <4>1. CASE lowlink[v] = num[v] /\ \E k \in 1..Len(t_stack) : t_stack[k] = v
        <5>. DEFINE k == CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = v
        <5>1. t_stack' = SubSeq(t_stack, k + 1, Len(t_stack))
          BY <2>5, <4>1, Zenon DEF check_root
        <5>2. k \in 1 .. Len(t_stack)
          BY <4>1
        <5>3. \A i \in k+1 .. Len(t_stack) : t_stack[i] \in Nodes /\ t_stack[i] = t_stack'[i - k]
          BY <2>5, <5>1, <5>2, <4>1 DEF check_root
        <5>. QED  BY  <2>5, <5>1, <5>2, <5>3, <4>1 DEF check_root
       <4>2. CASE ~(lowlink[v] = num[v] /\ \E k \in 1..Len(t_stack) : t_stack[k] = v)
         BY <2>5, <4>2, Zenon DEF check_root
       <4>. QED  BY <4>1, <4>2 DEF check_root
    <3>3. (num \in [Nodes -> Nat \cup {-1}])'
      BY <2>5 DEF check_root
    <3>4. (lowlink \in [Nodes -> Nat \cup {-1}])'
      BY <2>5 DEF check_root
    <3>5. (onStack \in [Nodes -> BOOLEAN])'
      BY <2>5 DEF check_root
    <3>6. (sccs \in SUBSET SUBSET Nodes)'
      <4>1. CASE lowlink[v] = num[v] /\ \E k \in 1..Len(t_stack) : t_stack[k] = v
        <5>1. sccs' = (sccs \cup {{t_stack[i] : i \in 1 .. (CHOOSE k \in 1..Len(t_stack) : t_stack[k] = v)}})
          BY <2>5, <4>1, Zenon DEF check_root
        <5>. QED  BY <5>1, <4>1
      <4>2. CASE ~(lowlink[v] = num[v] /\ \E k \in 1..Len(t_stack) : t_stack[k] = v)
        BY <2>5, <4>2, Zenon DEF check_root
      <4>. QED  BY <4>1, <4>2
    <3>7. (toVisit \in SUBSET Nodes)'
      BY <2>5 DEF check_root
    <3>8. (pc \in {"main", "Done", "start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"})'
      <4>1. Head(stack) \in StackEntry
        BY <2>5 DEF check_root
      <4>. QED  BY <4>1, <2>5 DEF StackEntry, check_root 
    <3>9. (stack \in Seq(StackEntry))'
      <4>1. stack # << >>
        BY <2>5 DEF check_root
      <4>. QED  BY <2>5, <4>1 DEF StackEntry, check_root
    <3>10. (\A i \in 1 .. Len(stack) :
               \/ /\ i < Len(stack)
                  /\ stack[i].pc = "continue_visit"
                  /\ stack[i].v \in Nodes /\ num[stack[i].v] \in Nat
                  /\ stack[i].succs \subseteq Succs[stack[i].v]
                  /\ stack[i].w \in Nodes /\ stack[i].w \in Succs[stack[i].v]
               \/ /\ i = Len(stack)
                  /\ stack[i].pc = "main"
                  /\ stack[i].v = defaultInitValue)'
      BY <2>5 DEF check_root
    <3>11. (\/ pc \in {"main", "Done"} /\ stack = << >>
            \/ /\ pc \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"}
               /\ stack # << >>)'
      <4>1. CASE pc' = "main"
        BY <2>5, <4>1 DEF check_root
      <4>2. CASE pc' = "continue_visit"
        <5>1. stack # << >> /\ Len(stack) - 1 # 0
          BY <2>5, <4>2 DEF check_root
        <5>4. Tail(stack) # << >>
          BY <5>1, HeadTailProperties, EmptySeq, Zenon
        <5> QED BY <5>1, <5>4, <4>2, <2>5 DEF check_root
      <4> QED BY <2>5, <4>1, <4>2 DEF check_root
    <3>12. (succs \in SUBSET Nodes)'
      <4>1. Head(stack) \in StackEntry
        BY <2>5 DEF check_root           
      <4>. QED  BY <4>1, <2>5 DEF StackEntry, check_root 
    <3>a. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"} => succs \subseteq Succs[v])'
      BY <2>5 DEF check_root
    <3>13. (pc = "check_root" => succs = {})'
      BY <2>5 DEF check_root
    <3>14. (v \in Nodes \cup {defaultInitValue})'
      BY <2>5 DEF check_root
    <3>15. (\/ pc \in {"main", "Done"} /\ v = defaultInitValue
            \/ /\ pc \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"}
               /\ v \in Nodes)'
      BY <2>5 DEF check_root
    <3>16. (pc = "start_visit" => num[v] = -1)'
      <4>0. pc' = Head(stack).pc 
        BY <2>5 DEF check_root
      <4>a. Head(stack).pc \in {"continue_visit", "main"}  
        <5>1. stack # << >>
            BY <2>5 DEF check_root
        <5>2.  Head(stack) \in StackEntry
            BY <2>5 DEF check_root
        <5> QED BY <2>5, <5>1, <5>2 DEF StackEntry, check_root  
      <4>1. pc' \in {"continue_visit", "main"} 
        BY <2>5, <4>0, <4>a  DEF check_root, StackEntry
      <4> QED BY <2>5, <4>1 DEF check_root, StackEntry
    <3>17. (pc = "visit_recurse" => num[w] = -1)'
     <4>1. pc' \in {"continue_visit", "main"}
        <5>1. stack # << >>
            BY <2>5 DEF check_root
        <5>2. Head(stack) \in StackEntry
            BY <2>5 DEF check_root 
        <5>3. pc' = Head(stack).pc
            BY <2>5 DEF check_root
        <5>4  Head(stack).pc \in {"continue_visit", "main"} 
            BY <2>5, <5>1, <5>2, <5>3 DEF check_root, StackEntry
        <5> QED BY <5>1, <5>2, <5>3, <5>4, <2>5 DEF check_root 
     <4> QED BY <2>5, <4>1 DEF check_root
    <3>18. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"} => num[v] \in Nat)'
       <4>1. pc' = Head(stack).pc 
         BY <2>5 DEF check_root
       <4>2. Head(stack).pc \in {"continue_visit", "main"}  
        <5>1. stack # << >>
            BY <2>5 DEF check_root
        <5>2.  Head(stack) \in StackEntry
            BY <2>5 DEF check_root
        <5> QED BY <2>5, <5>1, <5>2 DEF StackEntry, check_root  
       <4>3. pc' \in {"continue_visit", "main"} 
         BY <2>5, <4>1, <4>2  DEF check_root, StackEntry
       <4>4. UNCHANGED num
         BY <2>5 DEF check_root
       <4> QED BY <2>5, <4>3, <4>4 DEF check_root
    <3>19. (pc \in {"visit_recurse", "continue_visit"} => w \in Nodes /\ w \in Succs[v])'
      BY <2>5 DEF check_root
    <3>20. (w \in Nodes \cup {defaultInitValue})'
      <4>1. Head(stack) \in StackEntry
        BY <2>5 DEF check_root
      <4>. QED  BY <4>1, <2>5 DEF StackEntry, check_root 
    <3>21. QED
      BY <3>1, <3>10, <3>11, <3>12, <3>a, <3>13, <3>14, <3>15, <3>16, <3>17, <3>18, <3>19, <3>2, <3>20, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9
   
  <2>6. CASE main
    <3>1. (index \in Nat)'
      BY <2>6 DEF main
    <3>2. (t_stack \in Seq(Nodes))'
      BY <2>6 DEF main
    <3>3. (num \in [Nodes -> Nat \cup {-1}])'
      BY <2>6 DEF main
    <3>4. (lowlink \in [Nodes -> Nat \cup {-1}])'
      BY <2>6 DEF main
    <3>5. (onStack \in [Nodes -> BOOLEAN])'
      BY <2>6 DEF main
    <3>6. (sccs \in SUBSET SUBSET Nodes)'
      BY <2>6 DEF main
    <3>7. (toVisit \in SUBSET Nodes)'
      BY <2>6 DEF main
    <3>8. (pc \in {"main", "Done", "start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"})'
      BY <2>6 DEF main
    <3>9. (stack \in Seq(StackEntry))'
     <4>1. CASE stack' =  <<[procedure |-> "visit",
                                            pc |-> "main", succs |-> succs,
                                            w |-> w, v |-> v]>>
                                         \o stack
        BY <4>1 DEF StackEntry
      <4>2. CASE UNCHANGED stack
        BY <4>2
      <4>. QED  BY <4>1, <4>2, <2>6 DEF main
    <3>10. (\A i \in 1 .. Len(stack) :
               \/ /\ i < Len(stack)
                  /\ stack[i].pc = "continue_visit"
                  /\ stack[i].v \in Nodes /\ num[stack[i].v] \in Nat
                  /\ stack[i].succs \subseteq Succs[stack[i].v]
                  /\ stack[i].w \in Nodes /\ stack[i].w \in Succs[stack[i].v]
               \/ /\ i = Len(stack)
                  /\ stack[i].pc = "main"
                  /\ stack[i].v = defaultInitValue)'
      <4>1. CASE /\ stack' =  <<[procedure |-> "visit",
                                            pc |-> "main", succs |-> succs,
                                            w |-> w, v |-> v]>>
                                         \o stack 
                 /\ UNCHANGED num
        BY <4>1, <2>6 DEF main
      <4>2. CASE UNCHANGED <<stack, num>>
        BY <4>2
      <4>. QED  BY <4>1, <4>2, <2>6 DEF main
    <3>11. (\/ pc \in {"main", "Done"} /\ stack = << >>
            \/ /\ pc \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"}
               /\ stack # << >>)'
      BY <2>6 DEF main
    <3>12. (succs \in SUBSET Nodes)'
      BY <2>6 DEF main
    <3>a. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"} => succs \subseteq Succs[v])'
        BY <2>6 DEF main
    <3>13. (pc = "check_root" => succs = {})'
      BY <2>6 DEF main
    <3>14. (v \in Nodes \cup {defaultInitValue})'
      BY <2>6 DEF main
    <3>15. (\/ pc \in {"main", "Done"} /\ v = defaultInitValue
            \/ /\ pc \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"}
               /\ v \in Nodes)'
      BY <2>6 DEF main
    <3>16. (pc = "start_visit" => num[v] = -1)'
      BY <2>6 DEF main
    <3>17. (pc = "visit_recurse" => num[w] = -1)'
      BY <2>6 DEF main
    <3>18. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"} => num[v] \in Nat)'
      BY <2>6 DEF main
    <3>19. (pc \in {"visit_recurse", "continue_visit"} => w \in Nodes /\ w \in Succs[v])'
      BY <2>6 DEF main
    <3>20. (w \in Nodes \cup {defaultInitValue})'
      BY <2>6 DEF main
    <3>21. QED
      BY <3>1, <3>10, <3>11, <3>12, <3>a, <3>13, <3>14, <3>15, <3>16, <3>17, <3>18, <3>19, <3>2, <3>20, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 
    
  <2>7. CASE Terminating
    BY <2>7 DEF vars, Terminating
  <2>8. CASE UNCHANGED vars
    BY <2>8 DEF vars
  <2>9. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF Next, visit
<1>. QED  BY <1>init, <1>next, PTL DEF Spec

-----------------------------------------------------------------------------

NumStackInv ==
  /\ index <= Cardinality(Nodes)
  /\ \A n \in Nodes : num[n] < index
  /\ \A n \in Nodes : onStack[n] <=> \E i \in 1 .. Len(t_stack) : t_stack[i] = n
  /\ \A n \in Nodes : num[n] \in Nat <=> (onStack[n] \/ n \in UNION sccs)
  /\ \A i \in 1 .. Len(t_stack) : \A j \in 1 .. Len(t_stack) : 
        /\ i <= j <=> num[t_stack[j]] <= num[t_stack[i]]
        /\ t_stack[i] = t_stack[j] => i = j
  /\ index + Cardinality({n \in Nodes : num[n] = -1}) = Cardinality(Nodes)

THEOREM NumStack == Spec => []NumStackInv
<1>1. Init => NumStackInv
    <2> SUFFICES ASSUME Init
               PROVE  NumStackInv
        OBVIOUS
    <2>1. index <= Cardinality(Nodes)
        BY  FS_CardinalityType DEF Init, NumStackInv
    <2>2. \A n \in Nodes : num[n] < index
        BY DEF Init, NumStackInv
    <2>3. \A n \in Nodes : onStack[n] <=> \E i \in 1 .. Len(t_stack) : t_stack[i] = n
        BY DEF Init, NumStackInv
    <2>a. \A n \in Nodes : num[n] \in Nat <=> (onStack[n] \/ n \in UNION sccs)
        BY DEF Init, NumStackInv
    <2>4. \A i \in 1 .. Len(t_stack) : \A j \in 1 .. Len(t_stack) : 
           /\ i <= j <=> num[t_stack[j]] <= num[t_stack[i]]
           /\ t_stack[i] = t_stack[j] => i = j
        BY DEF Init, NumStackInv
    <2>5. index + Cardinality({n \in Nodes : num[n] = -1}) = Cardinality(Nodes)
        <3>1. Cardinality({n \in Nodes : num[n] = -1}) = Cardinality(Nodes)
            BY DEF Init, NumStackInv
        <3>2. index = 0
            BY DEF Init, NumStackInv
        <3> QED BY <3>1, <3>2, FS_CardinalityType DEF Init, NumStackInv
    <2>6. QED
        BY <2>1, <2>2, <2>3, <2>a, <2>4, <2>5 DEF NumStackInv
    
    
<1>2. TypeOK /\ NumStackInv /\ [Next]_vars => NumStackInv'
    <2>. USE DEF TypeOK, NumStackInv
    <2> SUFFICES ASSUME TypeOK,
                      NumStackInv,
                      [Next]_vars
               PROVE  NumStackInv'
        OBVIOUS
    <2>1. CASE start_visit
            <3>0. /\ IsFiniteSet({n \in Nodes : num[n] = -1})
                  /\ Cardinality({n \in Nodes : num[n] = -1}) \in Nat
              BY FS_Subset, FS_CardinalityType
            <3>1. index' <= Cardinality(Nodes)
                <4>1. {n \in Nodes : num[n] = -1} # {}
                  BY <2>1 DEF start_visit
                <4>2. Cardinality({n \in Nodes : num[n] = -1}) # 0
                  BY <4>1, <3>0, FS_EmptySet, Isa
                <4>3. index < Cardinality(Nodes)
                    BY <2>1, <3>0, <4>2, FS_CardinalityType DEF start_visit
                <4> QED BY <4>3, <2>1, FS_CardinalityType DEF start_visit 
            <3>2. \A n \in Nodes : num'[n] < index'
                BY <2>1  DEF start_visit
            <3>3. ASSUME NEW n \in Nodes
                  PROVE  onStack'[n] <=> \E i \in 1 .. Len(t_stack') : t_stack'[i] = n
                <4>1. CASE n = v
                    BY <2>1, <4>1 DEF start_visit
                <4>2. CASE n # v
                    <5>1. onStack'[n] = onStack[n]
                        BY <2>1, <4>2 DEF start_visit
                    <5>2. (\E i \in 1 .. Len(t_stack) : t_stack[i] = n) => (\E i \in 1 .. Len(t_stack') : t_stack'[i] = n)
                        BY <2>1, <4>2 DEF start_visit
                    <5> QED BY <2>1, <4>2, <5>1, <5>2 DEF start_visit
                <4> QED BY <2>1, <4>1, <4>2 DEF start_visit
            <3>a. \A n \in Nodes : num'[n] \in Nat <=> (onStack'[n] \/ n \in UNION sccs')
                BY <2>1 DEF start_visit
            <3>4. \A i \in 1 .. Len(t_stack') : \A j \in 1 .. Len(t_stack') : 
                    /\ i <= j <=> num'[t_stack'[j]] <= num'[t_stack'[i]]
                    /\ t_stack'[i] = t_stack'[j] => i = j
                <4> SUFFICES ASSUME NEW i \in 1 .. Len(t_stack'),
                                  NEW j \in 1 .. Len(t_stack')
                           PROVE  /\ i <= j <=> num'[t_stack'[j]] <= num'[t_stack'[i]]
                                  /\ t_stack'[i] = t_stack'[j] => i = j
                    OBVIOUS
                <4>1. i <= j <=> num'[t_stack'[j]] <= num'[t_stack'[i]]
                    <5>1. CASE t_stack'[i] = v
                        BY <2>1, <5>1 DEF start_visit
                    <5>2. CASE t_stack'[j] = v
                        BY <2>1, <5>2 DEF start_visit
                    <5>3. CASE  (t_stack'[i] = v \/ t_stack'[j] = v)
                        BY <2>1, <5>3 DEF start_visit
                    <5> QED BY <5>1, <5>2, <5>3, <2>1 DEF start_visit
                <4>2. t_stack'[i] = t_stack'[j] => i = j
                    <5>1. onStack[v] = FALSE
                        BY <2>1 DEF start_visit
                    <5>2. ~(\E ii \in 1 .. Len(t_stack)-1 : t_stack[ii] = v) 
                        BY <2>1 DEF start_visit
                    <5> QED BY <2>1, <5>1, <5>2 DEF start_visit
                <4>3. QED
                    BY <4>1, <4>2
            <3>5. index' + Cardinality({n \in Nodes : num'[n] = -1}) = Cardinality(Nodes)
                <4>1. /\ v \in Nodes /\ num[v] = -1 /\ num'[v] # -1
                      /\ \A n \in Nodes \ {v} : num'[n] = num[n]
                   BY <2>1 DEF start_visit
                <4>2. {n \in Nodes : num'[n] = -1} = {n \in Nodes : num[n] = -1} \ {v}
                   BY <4>1
                <4>3. Cardinality({n \in Nodes : num'[n] = -1}) = Cardinality({n \in Nodes : num[n] = -1}) - 1
                   BY <3>0, <4>1, <4>2, FS_RemoveElement, Isa
              <4> QED  BY <2>1, <4>3, <3>0 DEF start_visit
            <3> QED
                BY <2>1, <3>0, <3>1, <3>2, <3>3, <3>a, <3>4, <3>5 DEF start_visit
    <2>2. CASE explore_succ
        BY <2>2 DEF explore_succ
    <2>3. CASE visit_recurse
        BY <2>3 DEF visit_recurse
    <2>4. CASE continue_visit
        BY <2>4 DEF continue_visit
    <2>5. CASE check_root
        <3>1. index' <= Cardinality(Nodes)
            BY <2>5 DEF check_root
        <3>2. \A n \in Nodes : num'[n] < index'
            BY <2>5 DEF check_root
            
        <3>3. ASSUME NEW n \in Nodes
              PROVE  onStack'[n] <=> \E i \in 1 .. Len(t_stack') : t_stack'[i] = n
          <4>1. CASE lowlink[v] = num[v] /\ \E k \in 1 .. Len(t_stack) : t_stack[k] = v
            <5>. DEFINE k == CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = v
            <5>. k \in 1 .. Len(t_stack)
              BY <4>1
            <5>2. /\ onStack' = [nn \in Nodes |-> IF \E i \in 1 .. k : nn = t_stack[i] THEN FALSE
                                                  ELSE onStack[nn]]
                  /\ t_stack' = SubSeq(t_stack, k+1, Len(t_stack))
              BY <2>5, <4>1, Zenon DEF check_root
            <5>. HIDE DEF k
            <5>3. (\E i \in 1 .. Len(t_stack') : t_stack'[i] = n)
                  <=> (\E i \in k+1 .. Len(t_stack) : t_stack[i] = n)
              <6>1. ASSUME NEW i \in 1 .. Len(t_stack'), t_stack'[i] = n
                    PROVE  /\ i+k \in k+1 .. Len(t_stack)
                           /\ t_stack[i+k] = n
                BY <5>2, <6>1
              <6>2. ASSUME NEW i \in (k+1) .. Len(t_stack), t_stack[i] = n
                    PROVE  /\ i-k \in 1 .. Len(t_stack')
                           /\ t_stack'[i-k] = n
                BY <5>2, <6>2
              <6>. QED  BY <6>1, <6>2
            <5>4. onStack'[n] <=> (\E i \in k+1 .. Len(t_stack) : t_stack[i] = n)
              BY <5>2
            <5> QED  BY <5>3, <5>4
          <4>2. CASE ~(lowlink[v] = num[v] /\ \E k \in 1 .. Len(t_stack) : t_stack[k] = v)
            <5>1. UNCHANGED <<onStack, t_stack>>
                BY <2>5, <4>2, Zenon DEF check_root
            <5> QED BY <2>5, <4>2, <5>1  DEF check_root
          <4> QED BY <4>1, <4>2
        
        <3>a. ASSUME NEW n \in Nodes
              PROVE  num'[n] \in Nat <=> (onStack'[n] \/ n \in UNION sccs')
              
          <4>1. CASE lowlink[v] = num[v] /\ \E k \in 1 .. Len(t_stack) : t_stack[k] = v
            
            <5>. UNCHANGED num
              BY <2>5 DEF check_root
            <5>a. CASE num[n] \in Nat
            
                <6>. DEFINE k == CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = v
                <6>. k \in 1 .. Len(t_stack)
                    BY <4>1
                <6>2. /\ sccs' = (sccs \cup {{t_stack[i] : i \in 1 .. k}})
                      /\ onStack' = [nn \in Nodes |-> IF \E i \in 1 .. k : nn = t_stack[i] THEN FALSE
                                                  ELSE onStack[nn]]
                    BY <2>5, <4>1, Zenon DEF check_root
                <6>. HIDE DEF k
          
                <6>3. ASSUME ~onStack'[n]
                      PROVE  n \in UNION sccs'
                  <7>1. ~ onStack[n] \/ n \in {t_stack[i] : i \in 1 .. k}
                     BY <6>2, <6>3
                  <7>2. ~ onStack[n] => (n \in UNION sccs')
                    BY <5>a, <6>2
                  <7>3. (n \in {t_stack[i] : i \in 1 .. k}) => n \in UNION sccs'
                    BY <6>2, Isa
                  <7> QED BY <7>1, <7>2, <7>3
               <6> QED BY <6>3, <5>a     
            
            <5>b. CASE ~(num[n] \in Nat)  
                <6>. DEFINE k == CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = v
                <6>1. ~ onStack'[n]
                  <7>1. onStack' = [nn \in Nodes |-> IF \E i \in 1 .. k : nn = t_stack[i] THEN FALSE
                                                     ELSE onStack[nn]]
                    BY <2>5, <4>1, Zenon DEF check_root
                  <7>. QED  BY <5>b, <7>1
                <6>2. ~(n \in UNION sccs')
                    <7>1. sccs' = (sccs \cup {{t_stack[i] : i \in 1 .. k}})
                        BY <2>5, <4>1, Zenon DEF check_root
                    <7>. QED  BY <5>b, <7>1
                <6> QED BY <4>1, <5>b, <6>1, <6>2
                                    
            <5> QED  BY <5>a, <5>b
            
          <4>2. CASE ~(lowlink[v] = num[v] /\ \E k \in 1 .. Len(t_stack) : t_stack[k] = v) 
            <5>1. num[n] \in Nat <=> (onStack[n] \/ n \in UNION sccs)
                BY DEF NumStackInv
            <5>2. UNCHANGED <<num, onStack, sccs>>
                BY <2>5, <4>2 DEF check_root
            <5> QED BY <5>1, <5>2, <4>2, <2>5 DEF check_root
          <4> QED BY <4>1, <4>2
        
            
        <3>4.\A i \in 1 .. Len(t_stack') : \A j \in 1 .. Len(t_stack') : 
              /\ i <= j <=> num'[t_stack'[j]] <= num'[t_stack'[i]]
              /\ t_stack'[i] = t_stack'[j] => i = j
            <4> SUFFICES ASSUME NEW i \in 1 .. Len(t_stack'),
                              NEW j \in 1 .. Len(t_stack')
                       PROVE  /\ i <= j <=> num'[t_stack'[j]] <= num'[t_stack'[i]]
                              /\ t_stack'[i] = t_stack'[j] => i = j
                OBVIOUS
            <4>1. i <= j <=> num'[t_stack'[j]] <= num'[t_stack'[i]]
                <5>1. CASE lowlink[v] = num[v] /\ (\E k \in 1 .. Len(t_stack) : t_stack[k] = v)
                    <6> DEFINE k == CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = v
                    <6>. k \in 1 .. Len(t_stack)
                        BY <5>1
                    <6>0. t_stack' = SubSeq(t_stack, k+1, Len(t_stack))
                        BY <2>5, <5>1, Zenon DEF check_root
                    <6>2. /\ i \in k+1 .. Len(t_stack) => i \in 1 .. Len(t_stack') 
                          /\ j \in k+1 .. Len(t_stack) => j \in 1 .. Len(t_stack') 
                          BY <2>5, <5>1 DEF check_root
                    <6> QED BY <5>1, <2>5, <6>2, <6>0 DEF check_root
                <5>2. CASE ~(lowlink[v] = num[v] /\ \E k \in 1 .. Len(t_stack) : t_stack[k] = v) 
                    BY <5>2, <2>5, Zenon DEF check_root
                <5> QED BY <5>1, <5>2 
            <4>2. t_stack'[i] = t_stack'[j] => i = j
                <5>1. CASE lowlink[v] = num[v] /\ (\E k \in 1 .. Len(t_stack) : t_stack[k] = v)
                    <6> DEFINE k == CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = v
                    <6>. k \in 1 .. Len(t_stack)
                        BY <5>1
                    <6>0. t_stack' = SubSeq(t_stack, k+1, Len(t_stack))
                        BY <2>5, <5>1, Zenon DEF check_root
                    <6>2. /\ i \in k+1 .. Len(t_stack) => i \in 1 .. Len(t_stack') 
                          /\ j \in k+1 .. Len(t_stack) => j \in 1 .. Len(t_stack') 
                          BY <2>5, <5>1 DEF check_root
                    <6>3. (t_stack[i+k] = t_stack[j+k] => i+k = j+k) =>  (t_stack'[i] = t_stack'[j]  => i = j)
                          BY <2>5, <5>1, <6>0, <6>2 DEF check_root
                    <6> QED
                      <7>. HIDE DEF k
                      <7>. QED  BY <5>1, <2>5, <6>2, <6>0, <6>3 DEF check_root
                <5>2. CASE ~(lowlink[v] = num[v] /\ \E k \in 1 .. Len(t_stack) : t_stack[k] = v) 
                    BY <5>2, <2>5 DEF check_root
                <5> QED BY <5>1, <5>2 
            <4>. QED
                BY <4>1, <4>2
        <3>5. index' + Cardinality({n \in Nodes : num'[n] = -1}) = Cardinality(Nodes)
            BY <2>5 DEF  check_root
        <3> QED BY <2>5, <3>1, <3>2, <3>3, <3>a, <3>4, <3>5 DEF check_root
    <2>6. CASE main
        BY <2>6 DEF main
    <2>7. CASE Terminating
        BY <2>7 DEF vars, Terminating
    <2>8. CASE UNCHANGED vars
        BY <2>8 DEF vars 
    <2>9. QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF Next, visit
<1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

-----------------------------------------------------------------------------

(***************************************************************************)
(* Nodes are colored to monitor to what extent they have been explored.    *)
(* A node is white if its exploration has not yet started, it is gray if   *)
(* it is being explored, i.e. it is on the call stack or the currently     *)
(* visited node, and black otherwise.                                      *)
(***************************************************************************)
White == {n \in Nodes : num[n] \notin Nat}
Gray == {n \in Nodes : n = v \/ \E i \in 1 .. Len(stack) : n = stack[i].v}
Black == Nodes \ (White \cup Gray)

ColorInv ==
  /\ (* Nodes that are no longer in toVisit aren't white *)
     White \subseteq toVisit \cup (IF pc = "start_visit" THEN {v} ELSE {})
  /\ (* Successors of a visited node that are no longer in succs aren't white *)
     pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
     => White \cap Succs[v] \subseteq succs \cup (IF pc = "visit_recurse" THEN {w} ELSE {})
  /\ (* analogous condition for stack entries *)
     \A i \in 1 .. Len(stack) : stack[i].pc = "continue_visit" =>
          White \cap Succs[stack[i].v] 
          \subseteq stack[i].succs \cup (IF pc = "start_visit" /\ v = stack[i].w THEN {v} ELSE {})
  /\ (* black nodes do not have white successors *)
     \A n \in Black : Succs[n] \cap White = {}

THEOREM Color == Spec => []ColorInv
<1>1. Init => ColorInv
    BY DEF Init, ColorInv, White, Black, Gray
<1>2. TypeOK /\ ColorInv /\ [Next]_vars => ColorInv'
  <2>. USE DEF TypeOK, ColorInv, White, Black, Gray
  <2> SUFFICES ASSUME TypeOK,
                      ColorInv,
                      [Next]_vars
               PROVE  ColorInv'
    OBVIOUS
  <2>1. CASE start_visit
    BY <2>1, SMTT(20) DEF start_visit
  <2>2. CASE explore_succ
    BY <2>2 DEF explore_succ
  <2>3. CASE visit_recurse
    <3>1. (White \subseteq toVisit \cup (IF pc = "start_visit" THEN {v} ELSE {}))'
      BY <2>3 DEF visit_recurse
    <3>2. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => White \cap Succs[v] \subseteq succs \cup (IF pc = "visit_recurse" THEN {w} ELSE {}))'
      BY <2>3 DEF visit_recurse
    <3>3. (\A i \in 1 .. Len(stack) : stack[i].pc = "continue_visit" =>
                White \cap Succs[stack[i].v] 
                \subseteq stack[i].succs \cup (IF pc = "start_visit" /\ v = stack[i].w THEN {v} ELSE {}))'
      BY <2>3, SMTT(20) DEF visit_recurse
    <3>4. (\A n \in Black : Succs[n] \cap White = {})'
      BY <2>3, SMTT(20) DEF visit_recurse
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF ColorInv
  <2>4. CASE continue_visit
    BY <2>4 DEF continue_visit
  <2>5. CASE check_root
    <3>1. (White \subseteq toVisit \cup (IF pc = "start_visit" THEN {v} ELSE {}))'
      BY <2>5 DEF check_root
    <3>2. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => White \cap Succs[v] \subseteq succs \cup (IF pc = "visit_recurse" THEN {w} ELSE {}))'
      <4>a. pc' =  Head(stack).pc 
            BY <2>5 DEF check_root
      <4>b. Head(stack).pc \in {"continue_visit", "main"}
            <5>1. stack # << >>
                BY <2>5 DEF check_root
            <5>2. Head(stack) \in StackEntry
                BY <5>1
            <5>3. pc' = Head(stack).pc
                BY <2>5, <5>2 DEF check_root, StackEntry
            <5> QED BY <2>5, <5>1, <5>2 DEF StackEntry, check_root
      <4>1. CASE lowlink[v] = num[v] /\ \E k \in 1 .. Len(t_stack) : t_stack[k] = v
        BY <2>5, <4>1, <4>a, <4>b DEF check_root  
      <4>2. CASE ~(lowlink[v] = num[v] /\ \E k \in 1 .. Len(t_stack) : t_stack[k] = v)
        <5>1. pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => White \cap Succs[v] \subseteq succs \cup (IF pc = "visit_recurse" THEN {w} ELSE {})
            BY <2>5 DEF check_root
        <5>2. UNCHANGED <<num, sccs>>
            BY <2>5, <4>2 DEF check_root
        <5> QED BY <2>5, <4>2, <5>1, <5>2, <4>a, <4>b  DEF check_root
      <4> QED BY <2>5, <4>1, <4>2 DEF check_root
    <3>3. (\A i \in 1 .. Len(stack) : stack[i].pc = "continue_visit" =>
              White \cap Succs[stack[i].v] 
              \subseteq stack[i].succs \cup (IF pc = "start_visit" /\ v = stack[i].w THEN {v} ELSE {}))'
      BY <2>5 DEF check_root
    <3>4. (\A n \in Black : Succs[n] \cap White = {})'
      <4>1. White' = White
        BY <2>5 DEF check_root, White
      <4>2. Gray \subseteq Gray' \cup {v}
        <5>. SUFFICES ASSUME NEW i \in 1 .. Len(stack), stack[i].v \in Gray
                      PROVE  stack[i].v \in Gray'
          BY DEF Gray
        <5>1. CASE i = 1
          BY <5>1, <2>5 DEF check_root, Gray
        <5>2. CASE i \in 2 .. Len(stack)
          <6>1. /\ i-1 \in 1 .. Len(stack')
                /\ stack'[i-1] = stack[i]
            BY <5>2, <2>5 DEF check_root
          <6>. QED  BY <6>1 DEF Gray
        <5>. QED  BY <5>1, <5>2
      <4>3. Black' \subseteq Black \cup {v}
        BY <4>1, <4>2 DEF Black
      <4>4. Succs[v] \cap White = {}
        BY <2>5 DEF check_root
      <4>. QED  BY <4>1, <4>3, <4>4
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF ColorInv 
  <2>6. CASE main
    <3>1. (White \subseteq toVisit \cup (IF pc = "start_visit" THEN {v} ELSE {}))'
      BY <2>6 DEF main
    <3>2. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => White \cap Succs[v] \subseteq succs \cup (IF pc = "visit_recurse" THEN {w} ELSE {}))'
      BY <2>6 DEF main
    <3>3. (\A i \in 1 .. Len(stack) : stack[i].pc = "continue_visit" =>
              White \cap Succs[stack[i].v] 
              \subseteq stack[i].succs \cup (IF pc = "start_visit" /\ v = stack[i].w THEN {v} ELSE {}))'
      BY <2>6 DEF main, White, Gray, Black
    <3>4. (\A n \in Black : Succs[n] \cap White = {})'
      BY <2>6 DEF main, White, Gray, Black
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF ColorInv
  <2>7. CASE Terminating
    BY <2>7 DEF vars, Terminating
  <2>8. CASE UNCHANGED vars
    BY <2>8 DEF vars
  <2>9. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF Next, visit
<1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

---------------------------------------------------------------------------------------------

Precedes(x,y,seq) == \E i,j \in 1 .. Len(seq) : i <= j /\ seq[i] = x /\ seq[j] = y

Inv ==
  /\ \A i \in 1 .. Len(stack)-2 : stack[i].v \in Succs[stack[i+1].v]
  /\ Len(stack) > 1 => v \in Succs[stack[1].v]
  /\ \A i,j \in 1 .. Len(stack)-1 : 
        /\ i <= j <=> num[stack[j].v] <= num[stack[i].v]
        /\ stack[i].v = stack[j].v => i = j
  /\ \A i \in 1 .. Len(stack)-1 : num[stack[i].v] < index
  /\ pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
     => \A i \in 1 .. Len(stack)-1 : num[stack[i].v] < num[v]
  /\ \A i \in 1 .. Len(stack) : v # stack[i].v
  /\ Gray \subseteq Range(t_stack) \cup (IF pc = "start_visit" THEN {v} ELSE {})
  /\ \A i,j \in 1 .. Len(stack)-1 : i <= j => Precedes(stack[i].v, stack[j].v, t_stack)
  /\ pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
     => \A i \in 1 .. Len(stack)-1 : Precedes(v, stack[i].v, t_stack)
  /\ \A i \in 1 .. Len(stack)-1 : lowlink[stack[i].v] <= num[stack[i].v]
  /\ pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
     => onStack[v] /\ lowlink[v] <= num[v]
  /\ \A i \in 1 .. Len(t_stack) : lowlink[t_stack[i]] <= num[t_stack[i]]
  
THEOREM Stacks == Spec => []Inv
<1>1. Init => Inv
  BY DEF Init, Inv, Gray, Precedes
<1>2. TypeOK /\ NumStackInv /\ ColorInv /\ Inv /\ [Next]_vars => Inv'
  <2>. USE DEF TypeOK, NumStackInv, ColorInv, Black, Gray, White, Inv\*, Precedes
  <2> SUFFICES ASSUME TypeOK,
                      NumStackInv,
                      ColorInv,
                      Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. CASE start_visit
    <3>1. (\A i \in 1 .. Len(stack)-2 : stack[i].v \in Succs[stack[i+1].v])'
      BY <2>1 DEF start_visit
    <3>2. (Len(stack) > 1 => v \in Succs[stack[1].v])'
      BY <2>1 DEF start_visit
    <3>3. (\A i,j \in 1 .. Len(stack)-1 : 
              /\ i <= j <=> num[stack[j].v] <= num[stack[i].v]
              /\ stack[i].v = stack[j].v => i = j)'
      BY <2>1 DEF start_visit
    <3>a. (\A i \in 1 .. Len(stack)-1 : num[stack[i].v] < index)'
        BY <2>1 DEF start_visit
    <3>b. (\A i \in 1 .. Len(stack)-1 : num[stack[i].v] < num[v])'
        BY <2>1 DEF start_visit
    <3>4. (\A i \in 1 .. Len(stack) : v # stack[i].v)'
      BY <2>1 DEF start_visit
    <3>5. (Gray \subseteq Range(t_stack) \cup (IF pc = "start_visit" THEN {v} ELSE {}))'
        <4>1. Gray' = Gray
          BY <2>1 DEF start_visit, Gray
        <4>2. Range(t_stack') = {v} \cup Range(t_stack)
          <5>. t_stack' = <<v>> \o t_stack
            BY <2>1 DEF start_visit
          <5>. <<v>> \in Seq(Nodes) /\ Range(<<v>>) = {v}
            BY <2>1 DEF start_visit, Range
          <5>. QED  BY RangeConcatenation, Isa
        <4>3. pc = "start_visit" /\ pc' # "start_visit"
          BY <2>1 DEF start_visit
        <4>. QED  BY <4>1, <4>2, <4>3
    <3>6. (\A i,j \in 1 .. Len(stack)-1 : i <= j => Precedes(stack[i].v, stack[j].v, t_stack))'
      <4>0. /\ UNCHANGED stack
            /\ t_stack' = <<v>> \o t_stack
        BY <2>1 DEF start_visit
      <4> SUFFICES ASSUME NEW i \in 1 .. Len(stack)-1, NEW j \in 1 .. Len(stack)-1,
                          i <= j
                   PROVE  Precedes(stack[i].v, stack[j].v, t_stack')
        BY <4>0, Zenon
      <4>a. Precedes(stack[i].v, stack[j].v, t_stack)
        OBVIOUS
      <4>2. PICK ii,jj \in 1 .. Len(t_stack) : ii <= jj /\ t_stack[ii] = stack[i].v /\ t_stack[jj] = stack[j].v
        BY ONLY <4>a DEF Precedes
      <4>3. /\ ii+1 \in 1 .. Len(t_stack') /\ jj+1 \in 1 .. Len(t_stack')
            /\ ii+1 <= jj+1
            /\ t_stack'[ii+1] = stack[i].v
            /\ t_stack'[jj+1] = stack[j].v
        BY <4>0, <4>2
      <4>. QED  BY <4>3 DEF Precedes
    <3>7. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => \A i \in 1 .. Len(stack)-1 : Precedes(v, stack[i].v, t_stack))'
      <4>1. t_stack' = <<v>> \o t_stack
        BY <2>1 DEF start_visit
      <4> QED BY <2>1, <4>1 DEF start_visit, Precedes
    <3>8. (\A i \in 1 .. Len(stack)-1 : lowlink[stack[i].v] <= num[stack[i].v])'
      BY <2>1 DEF start_visit
    <3>9. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => onStack[v] /\ lowlink[v] <= num[v])'
      <4>1. onStack'[v] = TRUE
        BY <2>1 DEF start_visit
      <4>2. lowlink'[v] = index /\ num'[v] = index
        BY <2>1 DEF start_visit
      <4>3. UNCHANGED v
        BY <2>1 DEF start_visit
      <4> QED BY <2>1, <4>1, <4>2, <4>3 DEF start_visit
    <3>10. (\A i \in 1 .. Len(t_stack) : lowlink[t_stack[i]] <= num[t_stack[i]])'
      <4>1. t_stack' = <<v>> \o t_stack
        BY <2>1 DEF start_visit
      <4>2. lowlink'[v] = num'[v]
        BY <2>1 DEF start_visit
      <4> QED BY <2>1, <4>1, <4>2 DEF start_visit
    <3>11. QED
      BY <3>1, <3>10, <3>2, <3>3, <3>a, <3>b, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 
  <2>2. CASE explore_succ
    <3>1. (\A i \in 1 .. Len(stack)-2 : stack[i].v \in Succs[stack[i+1].v])'
      BY <2>2 DEF explore_succ
    <3>2. (Len(stack) > 1 => v \in Succs[stack[1].v])'
      BY <2>2 DEF explore_succ
    <3>3. (\A i,j \in 1 .. Len(stack)-1 : 
              /\ i <= j <=> num[stack[j].v] <= num[stack[i].v]
              /\ stack[i].v = stack[j].v => i = j)'
      BY <2>2 DEF explore_succ
    <3>a. (\A i \in 1 .. Len(stack)-1 : num[stack[i].v] < index)'
      BY <2>2 DEF explore_succ
    <3>b. (\A i \in 1 .. Len(stack)-1 : num[stack[i].v] < num[v])'
      BY <2>2 DEF explore_succ 
    <3>4. (\A i \in 1 .. Len(stack) : v # stack[i].v)'
      BY <2>2 DEF explore_succ
    <3>5. (Gray \subseteq Range(t_stack) \cup (IF pc = "start_visit" THEN {v} ELSE {}))'
      BY <2>2 DEF explore_succ
    <3>6. (\A i,j \in 1 .. Len(stack)-1 : i <= j => Precedes(stack[i].v, stack[j].v, t_stack))'
      BY <2>2 DEF explore_succ
    <3>7. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => \A i \in 1 .. Len(stack)-1 : Precedes(v, stack[i].v, t_stack))'
      BY <2>2 DEF explore_succ
    <3>8. (\A i \in 1 .. Len(stack)-1 : lowlink[stack[i].v] <= num[stack[i].v])'
      BY <2>2 DEF explore_succ
    <3>9. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => onStack[v] /\ lowlink[v] <= num[v])'
      BY <2>2 DEF explore_succ
    <3>10. (\A i \in 1 .. Len(t_stack) : lowlink[t_stack[i]] <= num[t_stack[i]])'
      <4>1. CASE succs # {}
        <5>1. CASE num[w'] = -1
            <6>1. CASE num[w'] < lowlink[v]
                BY <2>2, <4>1, <5>1, <6>1 DEF explore_succ
            <6>2. CASE  ~(num[w'] < lowlink[v])
                BY <2>2, <4>1, <5>1, <6>2 DEF explore_succ
            <6> QED BY <6>1, <6>2, <2>2, <4>1, <5>1 DEF explore_succ
        <5>2. CASE num[w'] # -1
            BY <2>2, <4>1, <5>2 DEF explore_succ
        <5> QED BY <2>2, <4>1, <5>1, <5>2 DEF explore_succ
      <4>2. CASE succs = {}
        BY <2>2, <4>2 DEF explore_succ
      <4> QED BY <2>2, <4>1, <4>2 DEF explore_succ
    <3>11. QED
      BY <3>1, <3>10, <3>2, <3>3, <3>a, <3>b, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Inv
    
  <2>3. CASE visit_recurse
    <3>1. (\A i \in 1 .. Len(stack)-2 : stack[i].v \in Succs[stack[i+1].v])'
      BY <2>3 DEF visit_recurse
    <3>2. (Len(stack) > 1 => v \in Succs[stack[1].v])'
      BY <2>3 DEF visit_recurse
    <3>3. (\A i,j \in 1 .. Len(stack)-1 : 
              /\ i <= j <=> num[stack[j].v] <= num[stack[i].v]
              /\ stack[i].v = stack[j].v => i = j)'
      <4> SUFFICES ASSUME NEW i \in (1 .. Len(stack)-1)', NEW j \in (1 .. Len(stack)-1)'
                   PROVE  (/\ i <= j <=> num[stack[j].v] <= num[stack[i].v]
                           /\ stack[i].v = stack[j].v => i = j)'
        OBVIOUS
      <4>1. (i <= j <=> num[stack[j].v] <= num[stack[i].v])'
        BY <2>3 DEF visit_recurse
      <4>2. (stack[i].v = stack[j].v => i = j)'
        BY <2>3 DEF visit_recurse
      <4>3. QED
        BY <4>1, <4>2
    <3>a. (\A i \in 1 .. Len(stack)-1 : num[stack[i].v] < index)'
      BY <2>3 DEF visit_recurse
    <3>b. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
      => (\A i \in 1 .. Len(stack)-1 : num[stack[i].v] < num[v]))'
      BY <2>3, Zenon DEF visit_recurse
    <3>4. (\A i \in 1 .. Len(stack) : v # stack[i].v)'
      <4>1. \A i \in 2 .. Len(stack) : v # stack[i].v
        BY <2>3 DEF visit_recurse
      <4>2. v # w
        BY <2>3 DEF visit_recurse 
      <4> QED BY <2>3, <4>1, <4>2 DEF visit_recurse
    <3>5. (Gray \subseteq Range(t_stack) \cup (IF pc = "start_visit" THEN {v} ELSE {}))'
      BY <2>3 DEF visit_recurse
    <3>6. (\A i,j \in 1 .. Len(stack)-1 : i <= j => Precedes(stack[i].v, stack[j].v, t_stack))'
      <4>. SUFFICES ASSUME NEW i \in 1 .. Len(stack')-1, NEW j \in 1 .. Len(stack')-1, i <= j
                    PROVE  Precedes(stack'[i].v, stack'[j].v, t_stack)
        BY <2>3 DEF visit_recurse
      <4>1. CASE i = 1 /\ j =1
        BY <4>1, <2>3 DEF visit_recurse, Precedes
      <4>2. CASE i = 1 /\ j \in 2 .. Len(stack')-1
        BY <4>2, <2>3 DEF visit_recurse
      <4>3. CASE i \in 2 .. Len(stack')-1
        BY <4>3, <2>3 DEF visit_recurse
      <4>. QED  BY <4>1, <4>2, <4>3
    <3>7. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => \A i \in 1 .. Len(stack)-1 : Precedes(v, stack[i].v, t_stack))'
      BY <2>3 DEF visit_recurse
    <3>8. (\A i \in 1 .. Len(stack)-1 : lowlink[stack[i].v] <= num[stack[i].v])'
      BY <2>3 DEF visit_recurse
    <3>9. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => onStack[v] /\ lowlink[v] <= num[v])'
      BY <2>3 DEF visit_recurse
    <3>10. (\A i \in 1 .. Len(t_stack) : lowlink[t_stack[i]] <= num[t_stack[i]])'
      BY <2>3 DEF visit_recurse
    <3>11. QED
      BY <3>1, <3>10, <3>2, <3>3, <3>a, <3>b, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Inv
    
  <2>4. CASE continue_visit
    <3>1. (\A i \in 1 .. Len(stack)-2 : stack[i].v \in Succs[stack[i+1].v])'
      BY <2>4 DEF continue_visit
    <3>2. (Len(stack) > 1 => v \in Succs[stack[1].v])'
      BY <2>4 DEF continue_visit
    <3>3. (\A i,j \in 1 .. Len(stack)-1 : 
              /\ i <= j <=> num[stack[j].v] <= num[stack[i].v]
              /\ stack[i].v = stack[j].v => i = j)'
      BY <2>4 DEF continue_visit
    <3>a. (\A i \in 1 .. Len(stack)-1 : num[stack[i].v] < index)'
      BY <2>4 DEF continue_visit
    <3>b. (\A i \in 1 .. Len(stack)-1 : num[stack[i].v] < num[v])'
      BY <2>4 DEF continue_visit
    <3>4. (\A i \in 1 .. Len(stack) : v # stack[i].v)'
      BY <2>4 DEF continue_visit
    <3>5. (Gray \subseteq Range(t_stack) \cup (IF pc = "start_visit" THEN {v} ELSE {}))'
      BY <2>4 DEF continue_visit
    <3>6. (\A i,j \in 1 .. Len(stack)-1 : i <= j => Precedes(stack[i].v, stack[j].v, t_stack))'
        BY <2>4 DEF continue_visit
    <3>7. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => \A i \in 1 .. Len(stack)-1 : Precedes(v, stack[i].v, t_stack))'
      <4>1. UNCHANGED <<v, stack, t_stack>>
        BY <2>4 DEF continue_visit
      <4> QED BY <2>4, <4>1 DEF continue_visit
    <3>8. (\A i \in 1 .. Len(stack)-1 : lowlink[stack[i].v] <= num[stack[i].v])'
      BY <2>4 DEF continue_visit
    <3>9. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => onStack[v] /\ lowlink[v] <= num[v])'
      BY <2>4 DEF continue_visit
    <3>10. (\A i \in 1 .. Len(t_stack) : lowlink[t_stack[i]] <= num[t_stack[i]])'
      BY <2>4 DEF continue_visit
    <3>11. QED
      BY <3>1, <3>10, <3>2, <3>3, <3>a, <3>b, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Inv
    
  <2>5. CASE check_root
    <3>1. (\A i \in 1 .. Len(stack)-2 : stack[i].v \in Succs[stack[i+1].v])'
      BY <2>5 DEF check_root
    <3>2. (Len(stack) > 1 => v \in Succs[stack[1].v])'
      BY <2>5 DEF check_root
    <3>3. (\A i,j \in 1 .. Len(stack)-1 : 
              /\ i <= j <=> num[stack[j].v] <= num[stack[i].v]
              /\ stack[i].v = stack[j].v => i = j)'
      BY <2>5 DEF check_root
    <3>a. (\A i \in 1 .. Len(stack)-1 : num[stack[i].v] < index)'
       BY <2>5 DEF check_root
    <3>b. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => \A i \in 1 .. Len(stack)-1 : num[stack[i].v] < num[v])'
       BY <2>5 DEF check_root
    <3>4. (\A i \in 1 .. Len(stack) : v # stack[i].v)'
      <4>1. v' = Head(stack).v
        BY <2>5 DEF check_root
      <4>2. stack' = Tail(stack)
        BY <2>5 DEF check_root
      <4>3. \A j \in 2 .. Len(stack) : Head(stack).v # stack[j].v
        OBVIOUS
      <4>. QED  BY <4>1, <4>2, <4>3
    <3>5. (Gray \subseteq Range(t_stack) \cup (IF pc = "start_visit" THEN {v} ELSE {}))'
      <4>1. CASE lowlink[v] = num[v] /\ (\E k \in 1 .. Len(t_stack) : t_stack[k] = v)
        <5>. DEFINE k == CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = v
        <5>. k \in 1 .. Len(t_stack) /\ t_stack[k] = v
          BY <4>1
        <5>. HIDE DEF k
        <5>. SUFFICES ASSUME NEW g \in Gray'
                      PROVE  g \in Range(t_stack)'
          OBVIOUS
        <5>1. PICK i \in 1 .. Len(stack)-1 : stack[i].v = g
          BY <2>5 DEF check_root, Gray
        <5>2. Precedes(v, stack[i].v, t_stack)
          BY <5>1, <2>5 DEF check_root
        <5>3. PICK l \in 1 .. Len(t_stack) : t_stack[l] = stack[i].v /\ k < l
          BY <5>2 DEF Precedes
        <5>4. t_stack' = SubSeq(t_stack, k+1, Len(t_stack))
          BY <2>5, <4>1 DEF check_root, k
        <5>5. /\ l-k \in DOMAIN t_stack'
              /\ t_stack'[l-k] = t_stack[l]
          BY <5>4, <5>3
        <5>. QED  BY <5>1, <5>3, <5>5 DEF Range
      <4>2. CASE ~(lowlink[v] = num[v] /\ (\E k \in 1 .. Len(t_stack) : t_stack[k] = v))
        <5>1. t_stack' = t_stack
          BY <4>2, <2>5 DEF check_root
        <5>. QED  BY <5>1, <4>2, <2>5 DEF check_root, Gray
      <4>. QED  BY <4>1, <4>2
    <3>6. (\A i,j \in 1 .. Len(stack)-1 : i <= j => Precedes(stack[i].v, stack[j].v, t_stack))'
      <4> SUFFICES ASSUME NEW i \in (1 .. Len(stack)-1)', NEW j \in (1 .. Len(stack)-1)',
                          (i <= j)'
                   PROVE  Precedes(stack[i].v, stack[j].v, t_stack)'
        OBVIOUS
      <4>a. stack' = Tail(stack)
        BY <2>5 DEF check_root
      <4>b. i \in 1 .. Len(stack)-1 => i \in 1 .. Len(stack)
        BY <2>5, <4>a DEF check_root
      <4>1. CASE lowlink[v] = num[v] /\ (\E k \in 1 .. Len(t_stack) : t_stack[k] = v)
      \* Prouver que si il existe un ii,jj tq t_stack[ii] = stack[i].v et t_stack[jj] = t_stack[j].v
      \* alors ii et jj \in k+1 ..  Len(t_stack)
        <5>. DEFINE k == CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = v
        <5>. k \in 1 .. Len(t_stack) /\ t_stack[k] = v
          BY <4>1
        <5>1.  t_stack' = SubSeq(t_stack, k+1, Len(t_stack))
        <5>. QED BY <5>1, <4>a, <4>b, <4>1, <2>5 DEF check_root
      <4>2. CASE ~(lowlink[v] = num[v] /\ (\E k \in 1 .. Len(t_stack) : t_stack[k] = v))
        <5>1. UNCHANGED t_stack
            BY <2>5, <4>2, Zenon DEF check_root
        <5> QED BY <2>5,<4>2, <4>a, <4>b, <5>1, HeadTailProperties DEF check_root
      <4> QED
        BY <2>5, <4>1, <4>2 DEF check_root
      
    <3>7. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => \A i \in 1 .. Len(stack)-1 : Precedes(v, stack[i].v, t_stack))'
(*****) BY <2>5 DEF check_root
    <3>8. (\A i \in 1 .. Len(stack)-1 : lowlink[stack[i].v] <= num[stack[i].v])'
        BY <2>5, HeadTailProperties DEF check_root
    <3>9. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => onStack[v] /\ lowlink[v] <= num[v])'
      <4>1. CASE lowlink[v] = num[v] /\ (\E k \in 1 .. Len(t_stack) : t_stack[k] = v)
        <5>. DEFINE k == CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = v
        <5>. k \in 1 .. Len(t_stack)
            BY <2>5 DEF check_root
        <5>1. UNCHANGED <<num, lowlink>>
(*****) <5> QED BY <2>5, <4>1, <5>1, HeadTailProperties DEF check_root
      <4>2. CASE ~(lowlink[v] = num[v] /\ (\E k \in 1 .. Len(t_stack) : t_stack[k] = v))
        <5>1. UNCHANGED <<onStack, num, lowlink>>
            BY <2>5, <4>2 DEF check_root
        <5>2. onStack[Head(stack).v]
            <6>1. \E i \in 1 .. Len(t_stack) : t_stack[i] = Head(stack).v
              BY <2>5 DEF check_root, Precedes
            <6> QED BY <2>5, <4>2, HeadTailProperties, <6>1 DEF check_root
(*****) <5> QED BY <2>5, <4>2, <5>1, <5>2 DEF check_root, StackEntry
      <4> QED BY <2>5, <4>1, <4>2 DEF check_root
    <3>10. (\A i \in 1 .. Len(t_stack) : lowlink[t_stack[i]] <= num[t_stack[i]])'
      <4> SUFFICES ASSUME NEW i \in (1 .. Len(t_stack))'
                   PROVE  (lowlink[t_stack[i]] <= num[t_stack[i]])'
        OBVIOUS
      <4>1. CASE lowlink[v] = num[v] /\ (\E k \in 1 .. Len(t_stack) : t_stack[k] = v)
        <5> DEFINE k == CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = v
        <5>. k \in 1 .. Len(t_stack)
            BY <4>1
        <5>1. t_stack' = SubSeq(t_stack, k+1, Len(t_stack))
            BY <2>5, <4>1, Zenon DEF check_root
        <5>2. i \in k+1 .. Len(t_stack) => i \in 1 .. Len(t_stack') 
            BY <2>5, <4>1 DEF check_root
        <5> QED BY <4>1, <2>5, <5>2, <5>1, SMTT(20) DEF check_root
      <4>2. CASE ~(lowlink[v] = num[v] /\ (\E k \in 1 .. Len(t_stack) : t_stack[k] = v))
        <5>1. UNCHANGED <<t_stack, num, lowlink>>
            BY <2>5, <4>2, Zenon DEF check_root
        <5> QED BY <2>5, <4>2, <5>1, HeadTailProperties DEF check_root, StackEntry
      <4> QED BY <2>5, <4>1, <4>2 DEF check_root
      
    <3>11. QED
      BY <3>1, <3>10, <3>2, <3>3, <3>a, <3>b, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF Inv
    
  <2>6. CASE main
    <3>a. CASE /\ stack' =  <<[procedure |-> "visit",
                                        pc |-> "main", succs |-> succs,
                                            w |-> w, v |-> v]>>
                                         \o stack 
                 /\ UNCHANGED num
        BY <3>a, <2>6 DEF main
    <3>b. CASE UNCHANGED <<stack, num>>
        BY <2>6, <3>b DEF main
    <3>1. (\A i \in 1 .. Len(stack)-2 : stack[i].v \in Succs[stack[i+1].v])'
        BY <3>a, <3>b, <2>6 DEF main
    <3>2. (Len(stack) > 1 => v \in Succs[stack[1].v])'
        BY <3>a, <3>b, <2>6 DEF main
    <3>3. (\A i,j \in 1 .. Len(stack)-1 : 
              /\ i <= j <=> num[stack[j].v] <= num[stack[i].v]
              /\ stack[i].v = stack[j].v => i = j)'
        BY <3>a, <3>b, <2>6 DEF main
    <3>x. (\A i \in 1 .. Len(stack)-1 : num[stack[i].v] < index)'
        BY <2>6, <3>a, <3>b DEF main
    <3>y. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => \A i \in 1 .. Len(stack)-1 : num[stack[i].v] < num[v])'
       BY <2>6 DEF main
    <3>4. (\A i \in 1 .. Len(stack) : v # stack[i].v)'
        BY <3>a, <3>b, <2>6 DEF main
    <3>5. (Gray \subseteq Range(t_stack) \cup (IF pc = "start_visit" THEN {v} ELSE {}))'
        BY <3>a, <3>b, <2>6 DEF main
    <3>6. (\A i,j \in 1 .. Len(stack)-1 : i <= j => Precedes(stack[i].v, stack[j].v, t_stack))'
        BY <3>a, <3>b, <2>6 DEF main
    <3>7. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => \A i \in 1 .. Len(stack)-1 : Precedes(v, stack[i].v, t_stack))'
      BY <2>6 DEF main
    <3>8. (\A i \in 1 .. Len(stack)-1 : lowlink[stack[i].v] <= num[stack[i].v])'
        BY <3>a, <3>b, <2>6 DEF main
    <3>9. (pc \in {"explore_succ", "visit_recurse", "continue_visit", "check_root"}
           => onStack[v] /\ lowlink[v] <= num[v])'
      BY <2>6 DEF main
    <3>10. (\A i \in 1 .. Len(t_stack) : lowlink[t_stack[i]] <= num[t_stack[i]])'
      BY <2>6 DEF main
    <3>11. QED
      BY <3>1, <3>10, <3>2, <3>3, <3>x, <3>y, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9
    
  <2>7. CASE Terminating
    BY <2>7 DEF Terminating, vars
  <2>8. CASE UNCHANGED vars
    BY <2>8 DEF vars
  <2>9. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, Zenon DEF Next, visit
    
<1> QED BY <1>1, <1>2, TypeCorrect, NumStack, Color, PTL DEF Spec

LEMMA StackConnected ==
  ASSUME TypeOK, Inv,
         NEW i \in 1 .. Len(stack)-1, NEW j \in 1 .. Len(stack)-1, i <= j
  PROVE  <<stack[j].v, stack[i].v>> \in Connected

LEMMA VConnected ==
  ASSUME TypeOK, Inv,
         Len(stack) > 1, NEW i \in 1 .. Len(stack)-1
  PROVE  <<stack[i].v, v>> \in Connected

LowlinkInv == 
  /\ \A x \in Nodes \ White : 
        /\ lowlink[x] # -1
        /\ \E y \in Nodes : /\ lowlink[x] = num[y]
                            /\ <<x,y>> \in Connected
                            /\ onStack[x] => onStack[y]
  /\ pc = "continue_visit" /\ lowlink[w] < lowlink[v] => onStack[w]
  /\ \A i \in 1 .. Len(stack)-1 : i#1 \/ pc # "start_visit" => onStack[stack[i].w]

StackReachabilityInv ==
  /\ \A x,y \in Nodes : onStack[x] /\ onStack[y] /\ num[x] <= num[y] => <<x,y>> \in Connected
  /\ \A y \in Nodes : onStack[y] => \E x \in Nodes : onStack[x] /\ num[x] <= num[y] /\ <<y,x>> \in Connected

THEOREM StackReachability == Spec => []StackReachabilityInv
<1>1. Init => StackReachabilityInv
<1>2. TypeOK /\ NumStackInv /\ StackReachabilityInv /\ [Next]_vars => StackReachabilityInv'
<1>. QED  BY TypeCorrect, NumStack, <1>1, <1>2, PTL DEF Spec

=============================================================================
\* Last modified Thu Mar 19 17:55:34 CET 2020 by Angela Ipseiz
\* Last modified Thu Mar 19 16:29:36 CET 2020 by Angela Ipseiz
\* Last modified Thu Mar 19 16:01:03 CET 2020 by merz
\* Last modified Thu Mar 19 15:22:11 CET 2020 by merz
\* Last modified Wed Mar 18 14:29:58 CET 2020 by Angela Ipseiz
\* Last modified Thu Mar 12 15:17:22 CET 2020 by merz
\* Last modified Thu Mar 12 10:56:53 CET 2020 by Angela Ipseiz
\* Last modified Thu Mar 05 12:10:08 CET 2020 by Angela Ipseiz
\* Last modified Tue Mar 03 11:04:54 CET 2020 by Angela Ipseiz
\* Created Thu Feb 20 14:43:38 CET 2020 by merz
