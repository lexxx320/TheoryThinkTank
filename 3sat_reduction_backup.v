(*This is an effort to reproduce the results presented in:
http://dl.acm.org/citation.cfm?id=976579
*)

Require Import Coq.Sets.Ensembles. 
Require Export Omega.             
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.  
Require Import hetList. 

Definition bvar := nat. (*boolean variables*)
Definition vvar := nat. (*vertex variables*)
Definition colors := nat. (*colors for graph vertices*) 
Definition edge : Type := prod vvar vvar. (*graph edges*)
 
(*boolean formula (n is the number of variables*)
Inductive bformula (n:nat) : Type :=
|pos : forall (x:bvar), x < n -> bformula n
|neg : forall (x:bvar), x < n -> bformula n
|conjForm : bformula n -> bformula n -> bformula n
|disjForm : bformula n -> bformula n -> bformula n. 

(*graph*)
Inductive graph (n:nat) : Type :=
|emptyGraph : graph n
|newEdge : forall (x1 x2 : vvar), x1 < n -> x2 < n -> graph n -> graph n
|gunion : graph n -> graph n -> graph n. 

(*environment (eta)*)
Definition env (A:Type) (B:Type) := list (A * B). 

(*Specificaion of SAT' satisfiability*)
Inductive SAT' (n:nat) : env bvar bool -> bformula n -> Prop :=
|satp : forall eta u p, In (u, true) eta -> SAT' n eta (pos n u p)
|satn : forall eta u p, In (u, false) eta -> SAT' n eta (neg n u p)
|satConj : forall eta F1 F2, SAT' n eta F1 -> SAT' n eta F2 -> SAT' n eta (conjForm n F1 F2)
|satDisj1 : forall eta F1 F2, SAT' n eta F1 -> SAT' n eta (disjForm n F1 F2)
|satDij2 : forall eta F1 F2, SAT' n eta F2 -> SAT' n eta (disjForm n F1 F2).

Fixpoint setVars n n' eta F :=
  match n with
      |0 => SAT' n' eta F
      |S n'' => (setVars n'' n' ((n'', true)::eta) F) \/ (setVars n'' n' ((n'', false)::eta) F)
  end. 

Definition SAT n F := setVars n n nil F. 

(*specification of graph coloring*)
Inductive coloring (n:nat) : env vvar colors -> graph n -> nat -> Prop :=
|cgempty : forall eta C, coloring n eta (emptyGraph n) C 
|cgEdge : forall eta C1 C2 C A B G p1 p2, In (A, C1) eta -> In (B, C2) eta ->
                                   C1 <= C -> C2 <= C -> C1 <> C2 -> coloring n eta G C ->
                                   coloring n eta (newEdge n A B p1 p2 G) C
|cgUnion : forall eta G1 G2 C, coloring n eta G1 C -> coloring n eta G2 C ->
                        coloring n eta (gunion n G1 G2) C. 

Inductive setVarsG (n:nat) : nat -> list (vvar * colors) -> graph n -> colors -> Prop :=
|setVarsEq : forall n' eta G C, n = n' -> coloring n eta  G C -> setVarsG n n' eta G C
|setVarsNeq : forall n' eta G C C', C < C' -> setVarsG n n' eta G C. 

(*-------------------------Reduction------------------------------*)
(*For every boolean variable in Delta, find the x that it maps to in Gamma and create
an edge from that x to to the vertex variable provided (X)*)
Inductive connectX (n:nat) : list (bvar * vvar * vvar * vvar) -> list bvar ->
                           vvar -> graph -> Prop :=
|connectXNil : forall Gamma X, connectX Gamma nil X emptyGraph
|connectX_vtx : forall Gamma Delta u v v' x' X G, 
                  In (u, v, v', x') Gamma -> connectX Gamma Delta X G -> 
                  connectX Gamma (u::Delta) X (newEdge (X, x') G). 

(*Same as above for makes edges to v and v' rather than x*)
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
         vars_to_clique Gamma (u::Delta) (gunion G1 (gunion G2 (gunion G3 G4))). 

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

(*mkEdge c u v v' e (determines if the edge from c goes to v or v')*)
Inductive mkEdge : vvar -> bformula -> vvar -> vvar -> edge -> Prop :=
|mkPos : forall c u v v', mkEdge c (pos u) v v' (c, v)
|mkNeg : forall c u v v', mkEdge c (neg u) v v' (c, v'). 

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

Theorem colorWeakening : forall eta G C, coloring eta G C -> coloring eta G (C+1). 
Proof.
  intros. induction H. 
  {constructor. }
  {apply cgVertex with (C' := C'). omega. assumption. }
  {apply cgEdge with (C1:=C1)(C2:=C2); auto; omega. }
  {apply cgUnion; auto. }
Qed. 

Fixpoint stackSAT eta s :=
  match s with
      |b::bs => SAT eta b /\ stackSAT eta bs 
      |nil => True
  end. 
(*
Let G be a graph; x1, x2, . . . , xn free vari- ables in G and u1,u2,...,un Boolean variables. Let ∆ = u1,u2,...,un and
Γ = (u1, , ,x1),(u2, , ,x2),...,(un, , ,xn)3.
If D :: Γ; ∆ ⊢ G CLIQUE and C ≥ c0 + n then there exists G :: η ⊢ G C COLORING where η = x1 → C1,x2 → C2,...,xn → Cn; Ci’s are distinct and Ci ≤ C.
*)

Ltac inv H := inversion H; subst; clear H.

Ltac invertHyp :=
  match goal with
      |H:exists x, ?e |- _ => inv H; try invertHyp
      |H:?x /\ ?y |- _ => inv H; try invertHyp
  end.

Theorem KColorNPC : forall Gamma Delta K F C eta C' G eta',
                      reduce Gamma Delta K F C C' G ->
                      (stackSAT eta K /\ SAT eta F <-> coloring eta' G C').
Proof.
  intros. split; intros. 
  {generalize dependent eta'. induction H; intros. 
   {simpl. invertHyp. inv H2. 
    {(*case1t*) eapply cgVertex with (C' := S C). 

Inductive uniqueColors (S:Ensemble colors) : env vvar colors -> Prop :=
|uniqueNil : uniqueColors S nil
|uniqueCons : forall x v l, uniqueColors (Add colors S v) l -> ~ Ensembles.In colors S v ->
                       uniqueColors S ((x, v)::l)
.

Fixpoint consistent (Gamma:list (bvar * vvar * vvar * vvar)) eta :=
  match Gamma with
      |(u,v,v',x)::Gamma => (exists C:colors, In (x, C) eta) /\ consistent Gamma eta
      |nil => True
  end. 

Theorem clique_color : forall n Gamma Delta G C eta, C >= n -> length eta = n -> uniqueColors (Empty_set colors) eta ->
                                      consistent Gamma eta -> clique Gamma Delta G -> coloring eta G C. 
Proof.
  intros. generalize dependent eta. generalize dependent C. generalize dependent n.
  induction H3; intros. 
  {constructor. }
  {constructor; eauto. 

Theorem consistentIn : forall Gamma u v v' x eta, In (u,v,v',x) Gamma -> consistent Gamma eta -> exists C, In (x, C) eta. 
Proof.
  induction Gamma; intros. 
  {inv H. }
  {inv H. simpl in *. invertHyp. exists x1. auto. destruct a. destruct p. destruct p.  simpl in *. 
   invertHyp. eauto. }
Qed. 

Theorem colorConnectX : forall n Gamma Delta G C x eta, C >= n -> length eta = n -> uniqueColors (Empty_set colors) eta ->
                                         connectX Gamma Delta x G -> coloring eta G C. 
Proof.
  intros. genDeps {{ n; C; eta }}. induction H2; intros. 
  {constructor. }
  {


clique_color : {C:nat} clique G -> coloring C G -> type.
%mode clique_color +C +CV -CG.
cliquec_base : clique_color z clique_# cg#.
cliquec_cont : {R:relate _ _ _ X}
                clique_color (s C) (clique_v R (D1 , D2) ^ V) (cgunion CG1 CG2)
                <- clique_color C D1 CG1’
                <- increase_color CG1’ CG1
                <- store_color X (s C) CGX
<- lemma5 E
<- connectX_color C CGX E D2 CG2.


case1t      : main_theorem C (c_new D) (satnewt E) F
                     (cgvertex ([v] [cgv] (cgvertex ([v’][cgv’]
                     (cgvertex ([x][cgx] (cgedge (CG v v’ x cgv cgv’ cgx)
                               <=z H !=z2 cgv’ cgv)) H)) <=z)) H)
                  <- ({u:v} {hypt: hyp u true}{v:vertex}{v’:vertex}{x:vertex}
                      {r:relate u v v’ x}{var: var u}{cgv :colorvertex v (s C)}
                      {cgv’:colorvertex v’ z}{cgx :colorvertex x (s C)}
                      store_color v (s C) cgv -> store_color v’ z cgv’ ->
                      store_color x (s C) cgx -> store_var u true hypt ->
                      main_theorem (s C) (D u v v’ x r ^ var) (E u hypt) F
                                                  (CG v v’ x cgv cgv’ cgx))
                  <- ({u:v}{v:vertex}{v’:vertex}{x:vertex}
                      {r:relate u v v’ x}{var: var u}
                         conv_invariant (D u v v’ x r ^ var) H).









