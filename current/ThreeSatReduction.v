(*This is an effort to reproduce the results presented in:
http://dl.acm.org/citation.cfm?id=976579
*)

Require Export Coq.Sets.Ensembles. 
Require Export Omega.             
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.  
Require Export hetList. 

Definition bvar := nat. (*boolean variables*)
Definition vvar := nat. (*vertex variables*)
Definition colors := nat. (*colors for graph vertices*) 
Definition edge : Type := prod vvar vvar. (*graph edges*)

(*boolean formula (n is the number of variables*)
Inductive bformula : Type :=
|pos :  bvar -> bformula 
|neg : bvar -> bformula
|conjForm : bformula -> bformula -> bformula
|disjForm : bformula -> bformula -> bformula. 

Inductive bformulaWF (n:nat) : bformula -> Prop :=
|posWF : forall x, x < n -> bformulaWF n (pos x)
|negWF : forall x, x < n -> bformulaWF n (neg x)
|conjWF : forall F1 F2, bformulaWF n F1 -> bformulaWF n F2 -> 
                   bformulaWF n (conjForm F1 F2).

(*graph*)
Inductive graph : Type :=
|emptyGraph : graph
|newEdge : vvar -> vvar -> graph -> graph
|gunion : graph -> graph -> graph. 

Inductive graphWF (n:nat) : graph -> Prop :=
|emptyWF : graphWF n emptyGraph
|newEWF : forall v1 v2 G, graphWF n G -> v1 < n -> v2 < n -> graphWF n (newEdge v1 v2 G)
|unionWF : forall G1 G2, graphWF n G1 -> graphWF n G2 -> graphWF n (gunion G1 G2). 

(*Specificaion of SAT' satisfiability*)
Inductive SAT' : list (bvar * bool) -> bformula -> Prop :=
|satp : forall eta u, In (u, true) eta -> SAT' eta (pos u)
|satn : forall eta u, In (u, false) eta -> SAT' eta (neg u)
|satConj : forall eta F1 F2, SAT' eta F1 -> SAT' eta F2 -> SAT' eta (conjForm F1 F2)
|satDisj1 : forall eta F1 F2, SAT' eta F1 -> SAT' eta (disjForm F1 F2)
|satDij2 : forall eta F1 F2, SAT' eta F2 -> SAT' eta (disjForm F1 F2).

Fixpoint setVars n eta F :=
  match n with
      |0 => SAT' eta F
      |S n'' => (setVars n'' ((n'', true)::eta) F) \/ 
               (setVars n'' ((n'', false)::eta) F)
  end. 

Inductive setVarsF (i:nat) : list (bvar * bool) -> bformula -> Prop :=
|setVarsDoneF : forall eta F, i = 0 -> SAT' eta F -> setVarsF i eta F
|setVarsConsF : forall eta F i', i = S i' -> setVarsF i' eta F -> setVarsF i ((i', false)::eta) F
|setVarsconsT : forall eta F i', i = S i' -> setVarsF i' eta F -> setVarsF i ((i',true)::eta) F. 

Definition SAT n F := setVars n nil F. 

(*specification of graph coloring*)
Inductive coloring : list (vvar * colors) -> graph -> nat -> Prop :=
|cgempty : forall eta C, coloring eta emptyGraph C 
|cgEdge : forall eta C1 C2 C A B G, In (A, C1) eta -> In (B, C2) eta ->
                             C1 <= C -> C2 <= C -> C1 <> C2 -> coloring eta G C ->
                             coloring eta (newEdge A B G) C
|cgUnion : forall eta G1 G2 C, coloring eta G1 C -> coloring eta G2 C ->
                        coloring eta (gunion G1 G2) C. 

Inductive setVarsG (i:nat) : list (vvar * colors) -> graph -> colors -> Prop :=
|setVarsDone : forall eta G C, i = 0 -> coloring eta G C -> setVarsG i eta G C
|setVarsNeq : forall eta G C C' i', i = S i' -> C' <= C -> setVarsG i' eta G C ->
                             setVarsG i ((i', C')::eta) G C. 
Fixpoint newE es G :=
  match es with
      |(e1,e2)::es => newEdge e1 e2 (newE es G)
      |_ => G
  end.  

(*-------------------------Reduction------------------------------*)
(*For every boolean variable in Delta, find the x that it maps to in Gamma and create
an edge from that x to to the vertex variable provided (X)*)
Inductive connectX : list (bvar * vvar * vvar * vvar) -> list bvar ->
                           vvar -> graph -> Prop :=
|connectXNil : forall Gamma X, connectX Gamma nil X emptyGraph
|connectX_vtx : forall Gamma Delta u v v' x' X G, 
                  In (u, v, v', x') Gamma -> connectX Gamma Delta X G -> 
                  connectX Gamma (u::Delta) X (newEdge X x' G). 

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
                         colors -> graph -> Prop :=
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

Fixpoint stackSAT (eta:list (bvar * bool)) s :=
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
