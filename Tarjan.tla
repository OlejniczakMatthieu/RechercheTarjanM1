------------------------------- MODULE Tarjan -------------------------------
EXTENDS FiniteSets, Sequences, Integers, SCC, TLAPS, FiniteSetTheorems

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
  /\ \A i \in 1 .. Len(stack) : stack[i].pc = "continue_visit" =>
        /\ i < Len(stack)
        /\ stack[i].v \in Nodes
        /\ stack[i].w \in Nodes
  /\ pc \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"} 
     => /\ stack # << >> 
        /\ Head(stack).pc = "continue_visit" => Head(stack).v \in Nodes 
        /\ Head(stack).pc = "continue_visit" => Head(stack).w \in Nodes
  /\ succs \in SUBSET Nodes
  /\ v \in Nodes \cup {defaultInitValue}
  /\ pc \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"} => v \in Nodes
  /\ pc \in {"visit_recurse", "continue_visit"} => w \in Nodes 
  /\ w \in Nodes \cup {defaultInitValue}

USE SuccsType

THEOREM Spec => []TypeOK
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
    BY <2>3 DEF StackEntry, visit_recurse
  <2>4. CASE continue_visit
    BY <2>4 DEF continue_visit
  <2>5. CASE check_root
        <3>1. index' \in Nat
            BY <2>5 DEF check_root
        <3>2. t_stack' \in Seq(Nodes) 
          <4>1. CASE lowlink[v] = num[v] /\ \E k \in 1..Len(t_stack) : t_stack[k] = v
            <5>1. t_stack' = SubSeq(t_stack,
                                (CHOOSE k \in 1..Len(t_stack) :
                                   t_stack[k] = v)
                                + 1, Len(t_stack))
              BY <2>5, <4>1 DEF check_root
            <5>2. (CHOOSE k \in 1..Len(t_stack) : t_stack[k] = v) \in 1..Len(t_stack)
              BY <4>1
            <5>. QED  BY  <5>1, <5>2, <4>1
          <4>2. CASE ~(lowlink[v] = num[v] /\ \E k \in 1..Len(t_stack) : t_stack[k] = v)
            BY <2>5, <4>2 DEF check_root
          <4>. QED  BY <4>1, <4>2
        <3>3. num' \in [Nodes -> Nat \cup {-1}]  
            BY <2>5 DEF check_root        
        <3>4. lowlink' \in [Nodes -> Nat \cup {-1}]  
            BY <2>5 DEF check_root         
        <3>5. onStack' \in [Nodes -> BOOLEAN] 
            BY <2>5 DEF check_root         
        <3>6. sccs' \in SUBSET SUBSET Nodes  
          <4>1. CASE lowlink[v] = num[v] /\ \E k \in 1..Len(t_stack) : t_stack[k] = v
            <5>1. sccs' = (sccs \cup {{t_stack[i] : i \in 1 .. (CHOOSE k \in 1..Len(t_stack) : t_stack[k] = v)}})
              BY <2>5, <4>1, Zenon DEF check_root
            <5>. QED  BY <5>1, <4>1
          <4>2. CASE ~(lowlink[v] = num[v] /\ \E k \in 1..Len(t_stack) : t_stack[k] = v)
            BY <2>5, <4>2, Zenon DEF check_root
          <4>. QED  BY <4>1, <4>2
        <3>7. toVisit' \in SUBSET Nodes  
            BY <2>5 DEF check_root        
        <3>8. pc' \in {"main", "Done", "start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"}
          <4>1. Head(stack) \in StackEntry
            BY <2>5 DEF check_root
          <4>. QED  BY <4>1, <2>5 DEF StackEntry, check_root 
        <3>9. stack' \in Seq(StackEntry)
          <4>1. stack # << >>
            BY <2>5 DEF check_root
          <4>. QED  BY <2>5, <4>1 DEF StackEntry, check_root
        <3>10. succs' \in SUBSET Nodes 
          <4>1. Head(stack) \in StackEntry
            BY <2>5 DEF check_root
          <4>. QED  BY <4>1, <2>5 DEF StackEntry, check_root 
        <3>11. /\ v' \in Nodes \cup {defaultInitValue}
               /\ w' \in Nodes \cup {defaultInitValue}
               /\ pc' \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"} => v' \in Nodes  
               /\ pc' \in {"visit_recurse", "continue_visit"} => w' \in Nodes
          <4>1. Head(stack) \in StackEntry
            BY <2>5 DEF check_root
          <4>. QED  BY <4>1, <2>5 DEF StackEntry, check_root 
        <3>12. pc' \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"} 
               => /\ stack' # <<>> 
                  /\ Head(stack').pc = "continue_visit" => Head(stack').v \in Nodes 
                  /\ Head(stack').pc = "continue_visit" => Head(stack').w \in Nodes
          <4> SUFFICES ASSUME pc' \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"}
                       PROVE  /\ stack' # << >> 
                              /\ Head(stack').pc = "continue_visit" => Head(stack').v \in Nodes 
                              /\ Head(stack').pc = "continue_visit" => Head(stack').w \in Nodes
                OBVIOUS
            <4>1. stack' # << >>
              <5>1. stack # << >>
                BY <2>5 DEF check_root
              <5>2. Head(stack) \in StackEntry
                BY <5>1
              <5>3. Head(stack).pc = "continue_visit"
                BY <2>5, <5>2 DEF check_root, StackEntry
              <5>4. 1 < Len(stack)
                BY <5>3, <5>1
              <5>5. Len(stack') = Len(stack)-1
                BY <2>5, <5>1 DEF check_root
              <5>. QED  BY <2>5, <5>4, <5>5
            <4>2. Head(stack').pc = "continue_visit" => Head(stack').v \in Nodes
                BY <2>5, <4>1 DEF check_root
            <4>3. Head(stack').pc = "continue_visit" => Head(stack').w \in Nodes
                BY <2>5, <4>1 DEF check_root
            <4>4. QED
                BY <4>1, <4>2, <4>3
        <3>13. \A i \in 1 .. Len(stack') : stack'[i].pc = "continue_visit" =>
                  /\ i < Len(stack')
                  /\ stack'[i].v \in Nodes
                  /\ stack'[i].w \in Nodes
          BY <2>5 DEF check_root
        <3>15. QED
            BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12, <3>13 DEF check_root
  
  <2>6. CASE main
    <3>1. index' \in Nat
        BY <2>6 DEF main
    <3>2. t_stack' \in Seq(Nodes) 
        BY <2>6 DEF main          
    <3>3. num' \in [Nodes -> Nat \cup {-1}]  
        BY <2>6 DEF main        
    <3>4. lowlink' \in [Nodes -> Nat \cup {-1}]  
        BY <2>6 DEF main         
    <3>5. onStack' \in [Nodes -> BOOLEAN] 
        BY <2>6 DEF main         
    <3>6. sccs' \in SUBSET SUBSET Nodes  
        BY <2>6 DEF main         
    <3>7. toVisit' \in SUBSET Nodes  
        BY <2>6 DEF main        
    <3>8. pc' \in {"main", "Done", "start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"} 
        BY <2>6 DEF main          
    <3>9. stack' \in Seq(StackEntry)  
      <4>1. CASE stack' =  <<[procedure |-> "visit",
                                            pc |-> "main", succs |-> succs,
                                            w |-> w, v |-> v]>>
                                         \o stack
        BY <4>1 DEF StackEntry
      <4>2. CASE UNCHANGED stack
        BY <4>2
      <4>. QED  BY <4>1, <4>2, <2>6 DEF main
    <3>10. succs' \in SUBSET Nodes 
        BY <2>6 DEF main
    <3>11. v' \in Nodes \cup {defaultInitValue}   
       BY <2>6 DEF main        
    <3>12. pc' \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"} => v' \in Nodes   
         BY <2>6 DEF main        
    <3>13. pc' \in {"visit_recurse", "continue_visit"} => w' \in Nodes   
         BY <2>6 DEF main        
    <3>14. w' \in Nodes \cup {defaultInitValue}
        BY <2>6 DEF main
    <3>15. \A i \in 1 .. Len(stack') : stack'[i].pc = "continue_visit" =>
              /\ i < Len(stack')
              /\ stack'[i].v \in Nodes
              /\ stack'[i].w \in Nodes
      <4>1. CASE stack' =  <<[procedure |-> "visit",
                                            pc |-> "main", succs |-> succs,
                                            w |-> w, v |-> v]>>
                                         \o stack
        BY <4>1
      <4>2. CASE UNCHANGED stack
        BY <4>2
      <4>. QED  BY <4>1, <4>2, <2>6 DEF main
    <3>16. pc' \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"} => 
             /\ stack' # << >> 
             /\ Head(stack').pc = "continue_visit" => Head(stack').v \in Nodes 
             /\ Head(stack').pc = "continue_visit" => Head(stack').w \in Nodes
      BY <2>6 DEF main
    <3>. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, <3>14, <3>15, <3>16 DEF main
  
  <2>7. CASE Terminating
    BY <2>7 DEF vars, Terminating
  <2>8. CASE UNCHANGED vars
    BY <2>8 DEF vars
  <2>9. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF Next, visit
<1>. QED  BY <1>init, <1>next, PTL DEF Spec

-----------------------------------------------------------------------------

NumStack ==
  /\ index <= Cardinality(Nodes)
  /\ \A n \in Nodes : num[n] < Cardinality(Nodes)
  /\ \A n \in Nodes : onStack[n] <=> (num[n] \in Nat /\ \E i \in 1 .. Len(t_stack) : t_stack[i] = n)
  /\ \A i \in 1 .. Len(t_stack) : \A j \in 1 .. Len(t_stack) : 
        /\ i <= j <=> num[t_stack[j]] <= num[t_stack[i]]
        /\ t_stack[i] = t_stack[j] => i = j

=============================================================================
\* Modification History
\* Last modified Thu Mar 12 16:34:22 CET 2020 by merz
\* Last modified Thu Mar 12 15:17:22 CET 2020 by merz
\* Last modified Thu Mar 12 14:13:39 CET 2020 by Angela Ipseiz
\* Last modified Thu Mar 12 10:56:53 CET 2020 by Angela Ipseiz
\* Last modified Thu Mar 05 12:10:08 CET 2020 by Angela Ipseiz
\* Last modified Tue Mar 03 11:04:54 CET 2020 by Angela Ipseiz
\* Created Thu Feb 20 14:43:38 CET 2020 by merz
