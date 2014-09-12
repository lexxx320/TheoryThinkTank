(*This is an effort to reproduce the results presented in:
http://dl.acm.org/citation.cfm?id=976579
*)

Require Export Omega.             
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.  

Definition bvar := nat. (*boolean variables*)
Definition vvar := nat. (*vertex variables*)
Definition colors := nat. (*colors for graph vertices*) 
Definition edge : Type := prod vvar vvar. (*graph edges*)

(*boolean formula*)
Inductive bformula : Type :=
|pos : bvar -> bformula
|neg : bvar -> bformula
|new : bvar -> bformula -> bformula
|conjForm : bformula -> bformula -> bformula
|disjForm : bformula -> bformula -> bformula. 

(*graph*)
Inductive graph : Type :=
|emptyGraph : graph
|newVertex : vvar -> graph -> graph
|newEdge : edge -> graph -> graph
|gunion : graph -> graph -> graph. 

(*environment (eta) mapping either boolean or vertex variables
**to their respective values (true/false or a color)*)
Inductive env {A:Type} : Type :=
|emptyEnv : env  
|consEnv : bvar -> A -> env -> env. 

(*lookup a variable in a given environment*)
Fixpoint lookup {A:Type} (e:@env A) bv :=
  match e with
      |emptyEnv => None
      |consEnv x v e' => if eq_nat_dec bv x
                         then Some v
                         else lookup e' bv
  end. 

(*Specificaion of SAT satisfiability*)
Inductive SAT : @env bool -> bformula -> Prop :=
|satp : forall eta u, lookup eta u = Some true -> SAT eta (pos u)
|satn : forall eta u, lookup eta u = Some false -> SAT eta (neg u)
|satConj : forall eta F1 F2, SAT eta F1 -> SAT eta F2 -> SAT eta (conjForm F1 F2)
|satDisj1 : forall eta F1 F2, SAT eta F1 -> SAT eta (disjForm F1 F2)
|satDij2 : forall eta F1 F2, SAT eta F2 -> SAT eta (disjForm F1 F2)
|satt : forall eta u F, SAT (consEnv u true eta) F -> SAT eta (new u F)
|satf : forall eta u F, SAT (consEnv u false eta) F -> SAT eta (new u F). 

(*specification of graph coloring*)
Inductive coloring : @env colors -> graph -> nat -> Prop :=
|cgempty : forall eta C, coloring eta emptyGraph C 
|cgVertex : forall eta C C' G v, C' <= C -> coloring (consEnv v C' eta) G C ->
                          coloring eta (newVertex v G) C
|cgEdge : forall eta C1 C2 C A B G, lookup eta A = Some C1 -> lookup eta B = Some C2 ->
                             C1 <= C -> C2 <= C -> C1 <> C2 -> coloring eta G C ->
                             coloring eta (newEdge (A, B) G) C
|cgUnion : forall eta G1 G2 C, coloring eta G1 C -> coloring eta G2 C ->
                        coloring eta (gunion G1 G2) C. 

Fixpoint newV vs G :=
  match vs with
      |v::vs => newVertex v (newV vs G)
      |nil => G
  end. 

Inductive connectX : list (bvar * vvar * vvar * vvar) -> list bvar ->
                     vvar -> graph -> Prop :=
|connectXNil : forall Gamma X, connectX Gamma nil X emptyGraph
|connectX_vtx : forall Gamma Delta u v v' x' X G, 
                  In (u, v, v', x') Gamma -> connectX Gamma Delta X G -> 
                  connectX Gamma (u::Delta) X (newEdge (X, x') G). 

Inductive connectV : list (bvar * vvar * vvar * vvar) -> list bvar ->
                      vvar -> graph -> Prop :=
|connectV_nil : forall Gamma X, connectV Gamma nil X emptyGraph
|connectV_vtx : forall Gamma Delta u v v' x' X G, 
                  In (u, v, v', x') Gamma -> connectV Gamma Delta X G ->
                  connectV Gamma (u::Delta) X (newEdge (X,v) (newEdge (X, v') G)). 

Inductive vars_to_clique : list (bvar * vvar * vvar * vvar) -> list bvar ->
                           graph -> Prop :=
|vars2cliqueNil : forall Gamma, vars_to_clique Gamma nil emptyGraph
|vars2cliqueVTX : forall Gamma Delta u v v' x G1 G2 G3 G4, 
         In (u,v,v',x) Gamma -> vars_to_clique Gamma Delta G1 ->
         connectX Gamma Delta v G2 -> connectX Gamma Delta v' G3 ->
         connectV Gamma Delta x G4 ->
         vars_to_clique Gamma (x::Delta) (gunion G1 (gunion G2 (gunion G3 G4))). 

Inductive clique : list (bvar * vvar * vvar * vvar) -> list bvar ->
                   graph -> Prop :=
|clique_empty : forall Gamma, clique Gamma nil emptyGraph
|clique_vtx : forall Gamma u v v' x Delta G1 G2, 
                In (u,v,v',x) Gamma -> clique Gamma Delta G1 -> connectX Gamma Delta x G2 ->
                clique Gamma (u::Delta) (gunion G1 G2). 

(*convert base (Gamma; Delta |- C Downarrow G*)
Inductive convert_base : list (bvar * vvar * vvar * vvar) -> list bvar ->
                         colors -> graph -> Prop :=
|conv'''_base : forall Gamma C, convert_base Gamma nil C emptyGraph
|conv'''_cont : forall Gamma Delta u v v' x C G,
                  In (u,v,v',x) Gamma -> convert_base Gamma Delta C G ->
                  convert_base Gamma (u::Delta) C (newEdge (C, v) (newEdge (C, v') G)). 

(*mkEdge c u v v' e*)
Inductive mkEdge : vvar -> bformula -> vvar -> vvar -> edge -> Prop :=
|mkPos : forall c u v v', mkEdge c (pos u) v v' (c, v)
|mkNeg : forall c u v v', mkEdge c (neg u) v v' (c, v'). 

Fixpoint newE es G :=
  match es with
      |e::es => newEdge e (newE es G)
      |nil => G
  end. 

Inductive convFormula : list (bvar * vvar * vvar * vvar) -> list bvar ->
                        bformula -> graph -> Prop := 
|conv'' : forall Gamma Delta u1 u2 u3 v1 v2 v3 v1' v2' v3' x1 x2 x3 c G e1 e2 e3 p1 p2 p3, 
            In (u1,v1,v1',x1) Gamma -> In (u2,v2,v2',x2) Gamma -> In (u3,v3,v3',x3) Gamma ->
            convert_base Gamma Delta c G -> mkEdge c p1 v1 v1' e1 -> mkEdge c p2 v2 v2' e2 ->
            mkEdge c p3 v3 v3' e3 -> 
            convFormula Gamma (u1::u2::u3::Delta) (disjForm p1 (disjForm p2 p3))
                        (newVertex c (newE [e1;e2;e3] G))
. 

(*Convert Stack of Continuations (Gamma; Delta |- K => G)*)
Inductive convStack : list (bvar * vvar * vvar * vvar) -> list bvar ->
                      list bformula -> graph -> Prop :=
|conv_base : forall Gamma Delta, convStack Gamma Delta nil emptyGraph
|conv_cons : forall Gamma Delta K F G1 G2, convStack Gamma Delta K G1 -> convFormula Gamma Delta F G2 ->
                              convStack Gamma Delta (F::K) (gunion G1 G2)
.

(*Top Level Reduction (Gamma; Delta |- K o F => C C' G)*)
Inductive reduce : list (bvar * vvar * vvar * vvar) -> list bvar ->
                   list bformula -> bformula -> nat -> nat -> graph -> Prop :=
|c_new : forall u v v' x Gamma Delta K F C C' G, 
           reduce ((u,v,v',x)::Gamma) (u::Delta) K F (C+1) C' G -> 
           reduce Gamma Delta K (new u F) C C' (newV [v;v';x] (newEdge (v,v') G))
|convConj : forall Gamma Delta K F F' C C' G, 
              reduce Gamma Delta (F::K) F' C C' G ->
              reduce Gamma Delta K (conjForm F F') C C' G
|convV : forall Gamma Delta K F1 F2 F3 G1 G2 G3 C,
         convStack Gamma Delta ((disjForm F1 (disjForm F2 F3))::K) G1 ->
         clique Gamma Delta G2 -> vars_to_clique Gamma Delta G3 ->
         reduce Gamma Delta K (disjForm F1 (disjForm F2 F3)) C C (gunion G1 (gunion G2 G3)).

Theorem reductionInvariant : forall K F G C C' Delta Gamma, 
                               reduce Gamma Delta K F C C' G -> C <= C'. 
Proof.
  intros. induction H; omega. 
Qed. 



















