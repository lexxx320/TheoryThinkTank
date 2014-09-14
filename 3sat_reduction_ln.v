(*This is an effort to reproduce the results presented in:
http://dl.acm.org/citation.cfm?id=976579

(Locally nameless representation)
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
Definition color := nat. (*colors for graph vertices*) 
Definition edge : Type := prod vvar vvar. (*graph edges*)
 
(*boolean formula (n is the number of variables*)
Inductive bformula : Type :=
|pos :  bvar -> bformula (*positive variables*)
|neg : bvar -> bformula  (*negative variable (~ x)*)
|const : bool -> bformula (*boolean constant*)
|conjForm : bformula -> bformula -> bformula  (*conjunction*)
|disjForm : bformula -> bformula -> bformula  (*disjunction*)
|newVar : bformula -> bformula.     (*bind new variable (de bruijn index) *)

Fixpoint openF k F (b:bool) := 
  match F with
      |pos x => if eq_nat_dec k x
               then (const b)
               else pos x
      |neg x => if eq_nat_dec k x
               then (const (negb b)) 
               else neg x
      |const b => const b
      |conjForm F1 F2 => conjForm (openF k F1 b) (openF k F2 b)
      |disjForm F1 F2 => disjForm (openF k F1 b) (openF k F2 b)
      |newVar F' => openF (S k) F' b 
  end. 

(*local closure*)
Inductive bformulaWF : bformula -> Prop :=
|constWF : forall b, bformulaWF (const b)
|conjWF : forall F1 F2, bformulaWF F1 -> bformulaWF F2 -> 
                   bformulaWF (conjForm F1 F2)
|disjWF : forall F1 F2, bformulaWF F1 -> bformulaWF F2 ->
                   bformulaWF (disjForm F1 F2)
|newWF : forall F,  bformulaWF (openF 0 F true) -> bformulaWF (newVar F). 

Inductive node : Type := varNode : nat -> node | colorNode : nat -> node. 

(*graph*)
Inductive graph : Type :=
|emptyGraph : graph
|newEdge : node -> node -> graph -> graph
|gunion : graph -> graph -> graph
|newVert : graph -> graph.  

Definition swapVar (v:node) (v':nat) (c:nat) : node := 
  match v with
      |varNode vn => if eq_nat_dec vn v'
                    then colorNode c
                    else v
      |colorNode _ => v
  end. 

(*replace all occurances of a bound variable with a color*)
Fixpoint openGraph (k:nat) (G:graph) (c:nat) : graph := 
  match G with
      |emptyGraph => emptyGraph
      |newEdge e1 e2 G' => newEdge (swapVar e1 k c) (swapVar e2 k c)
                                  (openGraph k G' c)
      |gunion G1 G2 => gunion (openGraph k G1 c) (openGraph k G2 c)
      |newVert G' => openGraph (S k) G' c
  end. 

Inductive graphWF : graph -> Prop :=
|emptyWF : graphWF emptyGraph
|newEWF : forall v1 v2 G, graphWF (newEdge (colorNode v1) (colorNode v2) G)
|unionWF : forall G1 G2, graphWF G1 -> graphWF G2 -> graphWF (gunion G1 G2)
|newVertWF : forall G, graphWF (openGraph 0 G 0) -> graphWF (newVert G). 

(*Specificaion of SAT' satisfiability*)
Inductive SAT : bformula -> Prop :=
|satConst : SAT (const true)
|satConj : forall F1 F2, SAT F1 -> SAT F2 -> SAT (conjForm F1 F2)
|satDisj1 : forall F1 F2, SAT F1 -> SAT (disjForm F1 F2)
|satDij2 : forall F1 F2, SAT F2 -> SAT (disjForm F1 F2)
|newVarT : forall F, SAT (openF 0 F true) -> SAT (newVar F)
|newVarF : forall F, SAT (openF 0 F false) -> SAT (newVar F). 

(*specification of graph coloring*)
Inductive coloring : graph -> nat -> Prop :=
|cgempty : forall C, coloring emptyGraph C 
|cgEdge : forall C1 C2 C G, C1 <= C -> C2 <= C -> C1 <> C2 -> 
                       coloring G C -> 
                       coloring (newEdge (colorNode C1) (colorNode C2) G) C
|cgUnion : forall G1 G2 C, coloring G1 C -> coloring G2 C ->
                      coloring (gunion G1 G2) C
|cgNewVert : forall G C C', C' <= C -> coloring (openGraph 0 G C') C ->
                       coloring (newVert G) C. 

(*-------------------------Reduction------------------------------*)
(*For every boolean variable in Delta, find the x that it maps to in Gamma and create
an edge from that x to to the vertex variable provided (X)*)
Inductive connectX : list (bvar * vvar * vvar * vvar) -> list bvar ->
                     vvar -> graph -> Prop :=
|connectXNil : forall Gamma X, connectX Gamma nil X emptyGraph
|connectX_vtx : forall Gamma Delta u v v' x' X G, 
                  In (u, v, v', x') Gamma -> connectX Gamma Delta X G -> 
                  connectX Gamma (u::Delta) X (newEdge (varNode X) (varNode x') G). 

(*Same as above for makes edges to v and v' rather than x*)
Inductive connectV : list (bvar * vvar * vvar * vvar) -> list bvar ->
                      vvar -> graph -> Prop :=
|connectV_nil : forall Gamma X, connectV Gamma nil X emptyGraph
|connectV_vtx : forall Gamma Delta u v v' x' X G, 
                  In (u, v, v', x') Gamma -> connectV Gamma Delta X G ->
                  connectV Gamma (u::Delta) X (newEdge X v (newEdge X v' G)). 

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
                         color -> graph -> Prop :=
|conv'''_base : forall Gamma C, convert_base Gamma nil C emptyGraph
|conv'''_cont : forall Gamma Delta u v v' x C G,
                  In (u,v,v',x) Gamma -> convert_base Gamma Delta C G ->
                  convert_base Gamma (u::Delta) C (newEdge C v (newEdge C v' G)). 

(*mkEdge c u v v' e (determines if the edge from c goes to v or v')*)
Inductive mkEdge : vvar -> bformula -> vvar -> vvar -> edge -> Prop :=
|mkPos : forall c u v v', mkEdge c (pos u) v v' (c, v)
|mkNeg : forall c u v v', mkEdge c (neg u) v v' (c, v'). 

Inductive convFormula (c:vvar) : list (bvar * vvar * vvar * vvar) -> list bvar ->
                        bformula -> graph -> Prop := 
|conv'' : forall Gamma Delta u1 u2 u3 v1 v2 v3 v1' v2' v3' x1 x2 x3 G e1 e2 e3 p1 p2 p3, 
            In (u1,v1,v1',x1) Gamma -> In (u2,v2,v2',x2) Gamma -> In (u3,v3,v3',x3) Gamma ->
            convert_base Gamma Delta c G -> mkEdge c p1 v1 v1' e1 -> mkEdge c p2 v2 v2' e2 ->
            mkEdge c p3 v3 v3' e3 -> 
            convFormula c Gamma (u1::u2::u3::Delta) (disjForm p1 (disjForm p2 p3))
                        (newE [e1;e2;e3] G)
. 

(*Convert Stack of Continuations (Gamma; Delta |- K => G)*)
Inductive convStack (i:vvar) : list (bvar * vvar * vvar * vvar) -> list bvar ->
                      list bformula -> graph -> Prop :=
|conv_base : forall Gamma Delta, convStack i Gamma Delta nil emptyGraph
|conv_cons : forall Gamma Delta K F G1 G2, convStack (i+1) Gamma Delta K G1 -> convFormula i Gamma Delta F G2 ->
                              convStack i Gamma Delta (F::K) (gunion G1 G2)
.

(*Top Level Reduction (Gamma; Delta |- K o F => C C' G)*)
Inductive reduce Gamma Delta : list bformula -> bformula -> nat -> nat -> graph -> Prop :=
(*|c_new : forall u v v' x Gamma Delta K F C C' G, 
           reduce ((u,v,v',x)::Gamma) (u::Delta) K F (C+1) C' G -> 
           reduce Gamma Delta K (new u F) C C' (newV [v;v';x] (newEdge (v,v') G)) *)
|convConj : forall K F F' C C' G, 
              reduce Gamma Delta (F::K) F' C C' G ->
              reduce Gamma Delta K (conjForm F F') C C' G
|convV : forall K F1 F2 F3 G1 G2 G3 C,
         convStack (length Gamma * 3) Gamma Delta ((disjForm F1 (disjForm F2 F3))::K) G1 ->
         clique Gamma Delta G2 -> vars_to_clique Gamma Delta G3 ->
         reduce Gamma Delta K (disjForm F1 (disjForm F2 F3)) C C (gunion G1 (gunion G2 G3)).

Fixpoint buildCtxt n := 
  match n with
      |S n' => 
       let (Gamma, Delta) := buildCtxt n'
       in ((n', 3 * n', 3 * n' + 1, 3 * n' + 2)::Gamma, n'::Delta)
      |0 => (nil, nil)
  end.

Definition Reduce F n : Prop := 
  let (Gamma, Delta) := buildCtxt n
  in reduce Gamma Delta nil F 0 (n+1) emptyGraph. 

Theorem reductionInvariant : forall K F G C C' Delta Gamma, 
                               reduce Gamma Delta K F C C' G -> C <= C'. 
Proof.
  intros. induction H; omega. 
Qed. 

Hint Constructors coloring. 

Theorem colorWeakening : forall eta G C, coloring eta G C -> coloring eta G (C+1). 
Proof.
  intros. induction H; eauto. econstructor; eauto; omega. 
Qed. 

Fixpoint stackSAT eta s :=
  match s with
      |b::bs => SAT' eta b /\ stackSAT eta bs 
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
                      (stackSAT eta K /\ SAT' eta F <-> coloring eta' G C').
Proof.
  intros. split; intros. 
  {generalize dependent eta'. induction H; intros. 
   {invertHyp. inv H2. apply IHreduce. simpl. auto. }
   {Admitted. 


Theorem KColorNPC' : forall Gamma Delta K F C eta n C' G eta',
                      Reduce F n ->
                      (SAT n F <-> setVarsG eta' G C').
Proof.


Inductive uniqueColor (S:Ensemble color) : env vvar color -> Prop :=
|uniqueNil : uniqueColor S nil
|uniqueCons : forall x v l, uniqueColor (Add color S v) l -> ~ Ensembles.In color S v ->
                       uniqueColor S ((x, v)::l)
.

Fixpoint consistent (Gamma:list (bvar * vvar * vvar * vvar)) eta :=
  match Gamma with
      |(u,v,v',x)::Gamma => (exists C:color, In (x, C) eta) /\ consistent Gamma eta
      |nil => True
  end. 

Theorem clique_color : forall n Gamma Delta G C eta, C >= n -> length eta = n -> uniqueColor (Empty_set color) eta ->
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

Theorem colorConnectX : forall n Gamma Delta G C x eta, C >= n -> length eta = n -> uniqueColor (Empty_set color) eta ->
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









