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
Require Export Coq.Program.Equality. 
Require Export Coq.Logic.Classical_Prop. 

Definition bvar := nat. (*boolean variables*)
Definition vvar := nat. (*vertex variables*)
Definition colors := nat. (*colors for graph vertices*) 
Definition edge : Type := prod vvar vvar. (*graph edges*)
 
(*boolean formula (n is the number of variables*)
Inductive atom : Type := pos : bvar -> atom | neg : bvar -> atom. 

Definition bformula := list (atom * atom * atom). 

(*graph*)
Inductive graph : Type :=
|emptyGraph : graph
|newEdge : vvar -> vvar -> graph -> graph
|gunion : graph -> graph -> graph. 

(*SAT atom is satisfiable*)
Inductive atomSAT : list (bvar * bool) -> atom -> Prop :=
|satp : forall eta u, In (u, true) eta -> atomSAT eta (pos u)
|satn : forall eta u, In (u, false) eta -> atomSAT eta (neg u). 

(*formula is satisfiable*)
Inductive SAT' : list (bvar * bool) -> bformula -> Prop :=
|satCons : forall a1 a2 a3 tl eta, (atomSAT eta a1 \/ atomSAT eta a2 \/ atomSAT eta a3) ->
                            SAT' eta tl -> SAT' eta ((a1,a2,a3)::tl)
|satNil : forall eta, SAT' eta nil. 

(*specification of graph coloring*)
Inductive coloring : list (vvar * colors) -> graph -> nat -> Prop :=
|cgempty : forall eta C, coloring eta emptyGraph C 
|cgEdge : forall eta C1 C2 C A B G, In (A, C1) eta -> In (B, C2) eta ->
                             C1 <= C -> C2 <= C -> C1 <> C2 -> coloring eta G C ->
                             coloring eta (newEdge A B G) C
|cgUnion : forall eta G1 G2 C, coloring eta G1 C -> coloring eta G2 C ->
                        coloring eta (gunion G1 G2) C. 

(*Recursively create new edges in a graph*)
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
|connectX_vtx : forall Gamma Delta u X G, 
                  In (u, 3*u, 3*u+1, 3*u+2) Gamma -> connectX Gamma Delta X G -> 
                  connectX Gamma (u::Delta) X (newEdge X (3*u+2) G). 

(*Same as above, but makes edges to v and v' rather than x*)
Inductive connectV : list (bvar * vvar * vvar * vvar) -> list bvar ->
                      vvar -> graph -> Prop :=
|connectV_nil : forall Gamma X, connectV Gamma nil X emptyGraph
|connectV_vtx : forall Gamma Delta u X G, 
                  In (u, 3*u, 3*u+1, 3*u+2) Gamma -> connectV Gamma Delta X G ->
                  connectV Gamma (u::Delta) X (newEdge X (3*u) (newEdge X (3*u+1) G)). 

(*Attach the v and v' variables to the clique created in the next set of rules*)
Inductive vars_to_clique : list (bvar * vvar * vvar * vvar) -> list bvar ->
                           graph -> Prop :=
|vars2cliqueNil : forall Gamma, vars_to_clique Gamma nil emptyGraph
|vars2cliqueVTX : forall Gamma Delta u G1 G2 G3 G4, 
         In (u,3*u,3*u+1,3*u+2) Gamma -> vars_to_clique Gamma Delta G1 ->
         connectX Gamma Delta (3*u) G2 -> connectX Gamma Delta (3*u+1) G3 ->
         connectV Gamma Delta (3*u+2) G4 ->
         vars_to_clique Gamma (u::Delta) (gunion G1 (gunion G2 (gunion G3 G4))). 

(*Create a clique out of the x variables*)
Inductive clique : list (bvar * vvar * vvar * vvar) -> list bvar ->
                   graph -> Prop :=
|clique_empty : forall Gamma, clique Gamma nil emptyGraph
|clique_vtx : forall Gamma u Delta G1 G2, 
                In (u,3*u,3*u+1,3*u+2) Gamma -> clique Gamma Delta G1 -> connectX Gamma Delta (3*u+2) G2 ->
                clique Gamma (u::Delta) (gunion G1 G2). 

(*convert base (Gamma; Delta |- C Downarrow G)*)
Inductive convert_base : list (bvar * vvar * vvar * vvar) -> list bvar ->
                         colors -> graph -> Prop :=
|conv'''_base : forall Gamma C, convert_base Gamma nil C emptyGraph
|conv'''_cont : forall Gamma Delta u C G,
                  In (u,3*u,3*u+1,3*u+2) Gamma -> convert_base Gamma Delta C G ->
                  convert_base Gamma (u::Delta) C (newEdge C (3*u) (newEdge C (3*u+1) G)). 

(*mkEdge c u v v' e (determines if the edge from c goes to v or v')*)
Inductive mkEdge : vvar -> atom -> vvar -> vvar -> edge -> Prop :=
|mkPos : forall c u v v', mkEdge c (pos u) v v' (c, v')
|mkNeg : forall c u v v', mkEdge c (neg u) v v' (c, v). 

Definition getVar a :=
  match a with
      |pos u => u
      |neg u => u
  end. 

Inductive convFormula (c:vvar) : list (bvar * vvar * vvar * vvar) -> list bvar ->
                        (atom * atom * atom) -> graph -> Prop := 
|conv'' : forall Gamma Delta u1 u2 u3 G e1 e2 e3 p1 p2 p3 D1 D2 D3 D4, 
            In (u1,3*u1,3*u1+1,3*u1+2) Gamma -> In (u2,3*u2,3*u2+1,3*u2+2) Gamma -> In (u3,3*u3,3*u3+1,3*u3+2) Gamma ->
            convert_base Gamma (D1++D2++D3++D4) c G -> 
            mkEdge c p1 (3*u1) (3*u1+1) e1 -> getVar p1 = u1 -> getVar p2 = u2 -> getVar p3 = u3 ->
            mkEdge c p2 (3*u2) (3*u2+1) e2 ->
            mkEdge c p3 (3*u3) (3*u3+1) e3 -> Delta = D1++[u1]++D2++[u2]++D3++[u3]++D4 -> 
            convFormula c Gamma Delta (p1, p2, p3)
                        (newE [e1;e2;e3] G)
. 

(*Convert Stack of Continuations (Gamma; Delta |- K => G)*)
Inductive convStack (i:vvar) : list (bvar * vvar * vvar * vvar) -> list bvar ->
                      bformula -> graph -> Prop :=
|conv_base : forall Gamma Delta, convStack i Gamma Delta nil emptyGraph
|conv_cons : forall Gamma Delta K F G1 G2, convStack (i+1) Gamma Delta K G1 -> convFormula i Gamma Delta F G2 ->
                              convStack i Gamma Delta (F::K) (gunion G1 G2)
.

(*Top Level Reduction (Gamma; Delta |- F => C C' G)*)
Inductive reduce Gamma Delta : bformula -> nat -> graph -> Prop :=
|convV : forall F G1 G2 G3 C,
         convStack (length Gamma * 3) Gamma Delta F G1 ->
         clique Gamma Delta G2 -> vars_to_clique Gamma Delta G3 ->
         reduce Gamma Delta F C (gunion G1 (gunion G2 G3)).

(*Build the Gamma and Delta contexts (n is the number of boolean variables in the formula we are reducing)*)
Inductive buildCtxt n : nat -> list (bvar*vvar*vvar*vvar) -> list bvar -> Prop :=
|buildCons : forall Gamma Delta i, buildCtxt n (S i) Gamma Delta -> 
                        buildCtxt n i ((i,3*i,3*i+1,3*i+2)::Gamma) (i::Delta)
|buildNil : buildCtxt n n nil nil. 

Theorem buildCtxtSanityChk : buildCtxt 3 0 [(0,0,1,2);(1,3,4,5);(2,6,7,8)] [0;1;2].
Proof.
  repeat constructor. 
Qed. 

Hint Constructors coloring. 

(*invert a hypothesis, substitute its pieces and clear it*)
Ltac inv H := inversion H; subst; clear H.

(*invert existentials and conjunctions in the entire proof context*)
Ltac invertHyp :=
  match goal with
      |H:exists x, ?e |- _ => inv H; try invertHyp
      |H:?x /\ ?y |- _ => inv H; try invertHyp
  end.

(*A list is unique with respect to some set U (usually Empty_set)*)
Inductive unique {A:Type} (U:Ensemble A) : list A -> Prop :=
|uniqueCons : forall hd tl, unique (Add A U hd) tl -> ~ Ensembles.In _ U hd ->
                       unique U (hd::tl)
|uniqueNil : unique U nil.

(*specifies that an atom is satisfiable, and gives back the appropriate color and 
**variable for setting the graph coloring environment*)
Inductive winner eta' eta : atom -> bvar -> colors -> Prop :=
|posWinner : forall c u, In (3*u, c) eta' -> In (u, true) eta -> winner eta' eta (pos u) u c
|negWinner : forall c u, In (3*u+1, c) eta' -> In (u, false) eta -> 
                    winner eta' eta (neg u) u c. 

(*Set the c_i variables in the graph coloring environment
** (c_i correspoinds to a clause in the boolean formula) *)
Inductive setCs env : nat -> bformula -> 
                        list (vvar * colors) -> list (bvar * bool) -> Prop := 
|fstSAT : forall u eta eta' c i a1 a2 a3 F,
            winner env eta a1 u c -> setCs env (S i) F eta' eta ->
            setCs env i ((a1, a2, a3)::F) ((i, c)::eta') eta
|sndSAT : forall u eta eta' c i a1 a2 a3 F,
            winner env eta a2 u c -> setCs env (S i) F eta' eta ->
            setCs env i ((a1, a2, a3)::F) ((i, c)::eta') eta
|thirdSAT : forall u eta eta' c i a1 a2 a3 F,
              winner env eta a3 u c -> setCs env (S i) F eta' eta -> 
            setCs env i ((a1, a2, a3)::F) ((i, c)::eta') eta
|setCsDone : forall i eta eta', setCs env i nil eta'  eta. 


(*N is the number of clauses in the boolean formula*)
(*specifies how a graph environment is built out of a boolean formula
**environment and reduction contexts*) 
Inductive setVertices : list (bvar*vvar*vvar*vvar) -> nat -> nat ->
                              list (vvar * colors) ->  list (bvar * bool) -> Prop :=
|setVerticesT : forall u eta eta' C Gamma, 
            setVertices Gamma C (S u) eta' eta-> u < C -> 
            setVertices ((u,3*u,3*u+1,3*u+2)::Gamma) C u 
                  ((3*u,u)::(3*u+1,C)::(3*u+2,u)::eta') ((u,true)::eta) 
|setVerticesF : forall u eta eta' C Gamma, 
            setVertices Gamma C (S u) eta' eta -> u < C ->
            setVertices ((u,3*u,3*u+1,3*u+2)::Gamma) C u
                  ((3*u,C)::(3*u+1,u)::(3*u+2,u)::eta') ((u, false)::eta) 
|setVerticesNil : forall C u, setVertices nil C u nil nil.

Theorem sanityCheck : setVertices [(0,0,1,2);(1,3,4,5);(2,6,7,8)]
                            3 0  [(0,0);(1,3);(2,0);(3,3);(4,1);(5,1);(6,2);(7,3);(8,2)]
                            [(0, true); (1, false); (2, true)].
Proof.
  repeat constructor.
Qed. 

(*Generates a graph coloring environment (valid might not be the greatest name 
**for this, but thats what they call it in the paper)*)
Inductive valid : list (bvar*vvar*vvar*vvar) -> nat -> bformula -> 
                  list (vvar * colors) -> list (bvar * bool) -> Prop :=
|valid_ : forall Gamma C eta eta' eta'' F res, setVertices Gamma C 0 eta' eta -> 
                          setCs eta' (3 * length Gamma) F eta'' eta ->
                          res = eta' ++ eta'' -> 
                          valid Gamma C F res eta. 

Theorem sanityCheck' : 
  valid [(0,0,1,2);(1,3,4,5);(2,6,7,8)]
              3  [(neg 0, pos 1, pos 2)] 
              [(0,0);(1,3);(2,0);(3,3);(4,1);(5,1);(6,2);(7,3);(8,2);(9,2)]
              [(0, true); (1, false); (2, true)].
Proof.
  econstructor. repeat econstructor. Focus 2. simpl. auto.
  eapply thirdSAT with (u:=2). simpl. apply posWinner. simpl. right. right. 
  right. right. right. right. auto. simpl. auto. constructor. 
Qed. 

(*Give the name of a hypothesis, and this tactic will copy it in the proof context*)
Ltac copy H := 
  match type of H with
      |?x => assert(x) by auto 
  end. 

(*negation distributes over disjunction*)
Theorem notDistr : forall A B, ~(A \/ B) <-> ~ A /\ ~ B. 
Proof.
  intros. split; intros. 
  {unfold not in H. split. intros c. apply H. auto. intros c. apply H; auto. }
  {unfold not in H. invertHyp. intros c. inv c. auto. auto. }
Qed. 

(*If something is in the set a list is unique with respect to, 
**then it can't be in the unique list*)
Theorem uniqueNotIn : forall A S (u:A) Delta,
                               Ensembles.In _ S u -> 
                               unique S Delta ->  ~ In u Delta. 
Proof.
  intros. induction H0. 
  {assert(u=hd \/ u <> hd). apply classic. inv H2. 
   {contradiction. }
   {simpl. rewrite notDistr. split. auto. apply IHunique. constructor. auto. }
  }
  {intros c. auto. }
Qed. 

(*invert tuple equality (this is a hack that only handles up to 4-arity)*)
Ltac invertTupEq := 
  match goal with
      |H:(?x1,?x2) = (?y1,?y2) |- _ => inv H; try invertTupEq
      |H:(?x1,?x2,?x3) = (?y1,?y2,?y3) |- _ => inv H; try invertTupEq
      |H:(?x1,?x2,?x3,?x4) = (?y1,?y2,?y3,?y4) |- _ => inv H; try invertTupEq
  end. 

(*invert a uniqueness hypothesis*)
Ltac invUnique :=
  match goal with
    |H:unique ?U (?x::?y) |- _ => inv H; try invUnique
  end. 

(*invert an assumption that something is in a list (creates two subgoals each time)*)
Ltac inCons :=
  match goal with
      |H:In ?X (?x::?y) |- _ => inv H
  end. 

(*If u is less than i (setVertices index) then its corresponding v, v', and x
**must not be in the graph coloring environment*)
Theorem notInEta' : forall Gamma C i eta' eta u epsilon c, 
                     setVertices Gamma C i eta' eta -> u < i -> 
                     (epsilon=0\/epsilon=1\/epsilon=2) -> 
                     ~ In (3 * u + epsilon, c) eta'. 
Proof.
  intros. genDeps {{ epsilon; u }}. induction H; intros. 
  {intros contra. inv contra.  
   {invertTupEq. omega. }
   {inCons. 
    {invertTupEq. omega. }
    {inCons.
     {invertTupEq. omega. }
     {assert(u0 < S u). omega. eapply IHsetVertices in H3; auto. }
    }
   }
  }
  {intros contra. inv contra.  
   {invertTupEq. omega. }
   {inCons. 
    {invertTupEq. omega. }
    {inCons.
     {invertTupEq. omega. }
     {assert(u0 < S u). omega. eapply IHsetVertices in H3; auto. }
    }
   }
  }
  {intros contra. inv contra. }
Qed. 

(*color a graph with a larger environment*)
Theorem colorWeakening : forall eta1 eta2 G C,
                           coloring eta1 G C ->
                           coloring (eta1++eta2) G C. 
Proof.
  intros. generalize dependent eta2. induction H; intros. 
  {constructor. }
  {econstructor. apply in_app_iff. eauto. apply in_app_iff. eauto. auto. auto. 
   auto. eauto. }
  {constructor; eauto. }
Qed. 

(*each x_i must map to u_i*)
Theorem XMapsToU : forall u Gamma C eta' eta i, 
                     In (u,3*u,3*u+1,3*u+2) Gamma -> 
                     setVertices Gamma C i eta' eta -> In (3*u+2,u) eta' /\ u < C.
Proof. 
  intros. induction H0. 
  {destruct (eq_nat_dec u u0). 
   {inCons. invertTupEq. simpl. split; auto. split. simpl. auto. omega. }
   {inCons. invertTupEq. omega. eapply IHsetVertices in H2; eauto. invertHyp. 
    split. simpl. auto. auto. }
  }
  {destruct (eq_nat_dec u u0). 
   {inCons. invertTupEq. simpl. split; auto. split. simpl. auto. omega. }
   {inCons. invertTupEq. omega. eapply IHsetVertices in H2; eauto. invertHyp. 
    split. simpl. auto. auto. }
  }
  {inv H. }
Qed. 

(*v_i and v_i' must map to either u_i or C, and must be distinct*)
Theorem V_V'MapToUOrC : forall u Gamma C eta' eta i, 
                          In (u,3*u,3*u+1,3*u+2) Gamma -> 
                          setVertices Gamma C i eta' eta -> 
                          (In (3*u,u) eta' /\ u < C /\ In (3*u+1,C) eta') \/
                          (In (3*u,C) eta' /\ u < C /\ In (3*u+1,u) eta').
Proof.
  intros. induction H0. 
  {destruct (eq_nat_dec u u0). 
   {subst. inCons. invertTupEq. left. simpl. auto. eapply IHsetVertices in H2. inv H2. 
    invertHyp. left. simpl. auto. invertHyp. left. simpl. auto. }
   {inCons. invertTupEq. omega. eapply IHsetVertices in H2. inv H2. invertHyp.
    left. split. simpl. auto. split. auto. simpl. auto. invertHyp. right. 
    simpl. split; auto. }
  }
  {destruct (eq_nat_dec u u0). 
   {subst. inCons. invertTupEq. right. simpl. auto. eapply IHsetVertices in H2. inv H2. 
    invertHyp. right. simpl. auto. invertHyp. right. simpl. auto. }
   {inCons. invertTupEq. omega. eapply IHsetVertices in H2. inv H2. invertHyp.
    left. split. simpl. auto. split. auto. simpl. auto. invertHyp. right. 
    simpl. split; auto. }
  }
  {inv H. }
Qed. 

(*color a graph with a larger environment*)
Theorem colorWeakeningApp : forall eta1 eta2 eta3 G C,
                           coloring (eta1++eta3) G C ->
                           coloring (eta1++eta2++eta3) G C. 
Proof.
  intros. genDeps {{ eta2 }}. remember(eta1++eta3). induction H; intros. 
  {constructor. }
  {subst. econstructor. apply in_app_iff in H. inv H. auto. apply in_app_iff; simpl.
   eauto. repeat rewrite in_app_iff. auto. apply in_app_iff in H0. inv H0; 
   repeat rewrite in_app_iff; eauto. auto. auto. auto. eapply IHcoloring; eauto. }
  {constructor; eauto. }
Qed. 
