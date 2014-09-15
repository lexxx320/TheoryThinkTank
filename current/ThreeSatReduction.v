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

Definition bvar := nat. (*boolean variables*)
Definition vvar := nat. (*vertex variables*)
Definition colors := nat. (*colors for graph vertices*) 
Definition edge : Type := prod vvar vvar. (*graph edges*)
 
(*boolean formula (n is the number of variables*)
Inductive atom : Type := pos : bvar -> atom | neg : bvar -> atom. 

Definition bformula := list (atom * atom * atom). 

Inductive atomWF (n:nat) : atom -> Prop :=
|posWF : forall x, x < n -> atomWF n (pos x)
|negWF : forall x, x < n -> atomWF n (neg x). 

Inductive bformulaWF (n:nat) : bformula -> Prop :=
|consWF : forall a1 a2 a3 tl, atomWF n a1 -> atomWF n a2 -> atomWF n a3 -> 
                         bformulaWF n tl -> bformulaWF n ((a1,a2,a3)::tl)
|nilWF : bformulaWF n nil. 

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

Inductive atomSAT : list (bvar * bool) -> atom -> Prop :=
|satp : forall eta u, In (u, true) eta -> atomSAT eta (pos u)
|satn : forall eta u, In (u, false) eta -> atomSAT eta (neg u). 

Inductive SAT' : list (bvar * bool) -> bformula -> Prop :=
|satCons : forall a1 a2 a3 tl eta, atomSAT eta a1 -> atomSAT eta a2 -> atomSAT eta a3 ->
                            SAT' eta tl -> SAT' eta ((a1,a2,a3)::tl)
|satNil : forall eta, SAT' eta nil. 

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
|connectX_vtx : forall Gamma Delta u X G, 
                  In (u, 3*u, 3*u+1, 3*u+2) Gamma -> connectX Gamma Delta X G -> 
                  connectX Gamma (u::Delta) X (newEdge X (3*u+2) G). 

(*Same as above for makes edges to v and v' rather than x*)
Inductive connectV : list (bvar * vvar * vvar * vvar) -> list bvar ->
                      vvar -> graph -> Prop :=
|connectV_nil : forall Gamma X, connectV Gamma nil X emptyGraph
|connectV_vtx : forall Gamma Delta u X G, 
                  In (u, 3*u, 3*u+1, 3*u+2) Gamma -> connectV Gamma Delta X G ->
                  connectV Gamma (u::Delta) X (newEdge X (3*u) (newEdge X (3*u+1) G)). 

Inductive vars_to_clique : list (bvar * vvar * vvar * vvar) -> list bvar ->
                           graph -> Prop :=
|vars2cliqueNil : forall Gamma, vars_to_clique Gamma nil emptyGraph
|vars2cliqueVTX : forall Gamma Delta u G1 G2 G3 G4, 
         In (u,3*u,3*u+1,3*u+2) Gamma -> vars_to_clique Gamma Delta G1 ->
         connectX Gamma Delta (3*u) G2 -> connectX Gamma Delta (3*u+1) G3 ->
         connectV Gamma Delta (3*u+2) G4 ->
         vars_to_clique Gamma (u::Delta) (gunion G1 (gunion G2 (gunion G3 G4))). 

Inductive clique : list (bvar * vvar * vvar * vvar) -> list bvar ->
                   graph -> Prop :=
|clique_empty : forall Gamma, clique Gamma nil emptyGraph
|clique_vtx : forall Gamma u Delta G1 G2, 
                In (u,3*u,3*u+1,3*u+2) Gamma -> clique Gamma Delta G1 -> connectX Gamma Delta (3*u+2) G2 ->
                clique Gamma (u::Delta) (gunion G1 G2). 

(*convert base (Gamma; Delta |- C Downarrow G*)
Inductive convert_base : list (bvar * vvar * vvar * vvar) -> list bvar ->
                         colors -> graph -> Prop :=
|conv'''_base : forall Gamma C, convert_base Gamma nil C emptyGraph
|conv'''_cont : forall Gamma Delta u C G,
                  In (u,3*u,3*u+1,3*u+2) Gamma -> convert_base Gamma Delta C G ->
                  convert_base Gamma (u::Delta) C (newEdge C (3*u) (newEdge C (3*u+1) G)). 

(*mkEdge c u v v' e (determines if the edge from c goes to v or v')*)
Inductive mkEdge : vvar -> atom -> vvar -> vvar -> edge -> Prop :=
|mkPos : forall c u v v', mkEdge c (pos u) v v' (c, v)
|mkNeg : forall c u v v', mkEdge c (neg u) v v' (c, v'). 

Inductive convFormula (c:vvar) : list (bvar * vvar * vvar * vvar) -> list bvar ->
                        (atom * atom * atom) -> graph -> Prop := 
|conv'' : forall Gamma Delta u1 u2 u3 G e1 e2 e3 p1 p2 p3, 
            In (u1,3*u1,3*u1+1,3*u1+2) Gamma -> In (u2,3*u2,3*u2+1,3*u2+2) Gamma -> In (u3,3*u3,3*u3+1,3*u3+2) Gamma ->
            convert_base Gamma Delta c G -> mkEdge c p1 (3*u1) (3*u1+1) e1 -> mkEdge c p2 (3*u2) (3*u2+1) e2 ->
            mkEdge c p3 (3*u3) (3*u3+1) e3 -> 
            convFormula c Gamma (u1::u2::u3::Delta) (p1, p2, p3)
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

Inductive buildCtxt n : nat -> list (bvar*vvar*vvar*vvar) -> list bvar -> Prop :=
|buildCons : forall Gamma Delta i, buildCtxt n (S i) Gamma Delta -> 
                        buildCtxt n i ((i,3*i,3*i+1,3*i+2)::Gamma) (i::Delta)
|buildNil : buildCtxt n n nil nil. 

Theorem buildCtxtSanityChk : buildCtxt 3 0 [(0,0,1,2);(1,3,4,5);(2,6,7,8)] [0;1;2].
Proof.
  repeat constructor. 
Qed. 

Hint Constructors coloring. 

Theorem colorWeakening : forall eta G C, coloring eta G C -> coloring eta G (C+1). 
Proof.
  intros. induction H; eauto. econstructor; eauto; omega. 
Qed. 

Ltac inv H := inversion H; subst; clear H.

Ltac invertHyp :=
  match goal with
      |H:exists x, ?e |- _ => inv H; try invertHyp
      |H:?x /\ ?y |- _ => inv H; try invertHyp
  end.

(*a generic specification of uniqueness (typically f is used to project
**out of a tuple)*)
Inductive genericUnique {A B :Type} (U:Ensemble B) (f:A -> B) : list A -> Prop :=
|uniqueCons : forall hd tl, genericUnique (Add B U (f hd)) f tl ->
                       ~ Ensembles.In _ U (f hd) -> genericUnique U f (hd::tl)
|uniqueNil : genericUnique U f nil. 

Inductive winner eta : atom -> bvar -> Prop :=
|posWinner : forall x, In (x, true) eta -> winner eta (pos x) x
|negWinner : forall x, In (x, false) eta -> winner eta (neg x) x. 

Inductive setCs env : list (bvar*vvar*vvar*vvar) -> nat -> bformula -> 
                        list (vvar * colors) -> list (bvar * bool) -> Prop := 
|fstSAT : forall u eta eta' c i Gamma a1 a2 a3 F,
            In (u, c) env -> winner eta a1 u -> setCs env Gamma (S i) F eta' eta ->
            setCs env Gamma i ((a1, a2, a3)::F) ((i, c)::eta') eta
|sndSAT : forall u eta eta' c i Gamma a1 a2 a3 F,
            In (u, c) env -> winner eta a2 u -> setCs env Gamma (S i) F eta' eta ->
            setCs env Gamma i ((a1, a2, a3)::F) ((i, c)::eta') eta
|thirdSAT : forall u eta eta' c i Gamma a1 a2 a3 F,
            In (u, c) env -> winner eta a3 u -> setCs env Gamma (S i) F eta' eta -> 
            setCs env Gamma i ((a1, a2, a3)::F) ((i, c)::eta') eta
|setCsDone : forall i Gamma eta eta', setCs env Gamma i nil eta'  eta. 


(*N is the number of clauses in the boolean formula*)
(*specifies how a graph environment is built out of a boolean formula
**environment and reduction contexts*) 
Inductive setVertices : list (bvar*vvar*vvar*vvar) -> nat -> nat ->
                  list (vvar * colors) ->  list (bvar * bool) -> Prop :=
|setVerticesT : forall u eta eta' C Gamma, 
            setVertices Gamma C (S u) eta' eta -> u <= C -> 
            setVertices ((u,3*u,3*u+1,3*u+2)::Gamma) C u 
                  ((3*u,u)::(3*u+1,C)::(3*u+2,u)::eta') ((u,true)::eta)
|setVerticesF : forall u eta eta' C Gamma, 
            setVertices Gamma C (S u) eta' eta -> u <= C ->
            setVertices ((u,3*u,3*u+1,3*u+2)::Gamma) C u
                  ((3*u,C)::(3*u+1,u)::(3*u+2,u)::eta') ((u, false)::eta)
|setVerticesNil : forall C u, setVertices nil C u nil nil.

Theorem sanityCheck : setVertices [(0,0,1,2);(1,3,4,5);(2,6,7,8)]
                            3 0  [(0,0);(1,3);(2,0);(3,3);(4,1);(5,1);(6,2);(7,3);(8,2)]
                            [(0, true); (1, false); (2, true)].
Proof.
  repeat constructor.
Qed. 

Inductive valid : list (bvar*vvar*vvar*vvar) -> nat -> bformula -> 
                  list (vvar * colors) -> list (bvar * bool) -> Prop :=
|valid_ : forall Gamma C eta eta' eta'' F res, setVertices Gamma C 0 eta' eta -> 
                          setCs eta' Gamma (3 * length Gamma) F eta'' eta ->
                          res = eta' ++ eta'' -> 
                          valid Gamma C F res eta. 

Theorem sanityCheck' : 
  valid [(0,0,1,2);(1,3,4,5);(2,6,7,8)]
              3  [(neg 0, pos 1, pos 2)]
              [(0,0);(1,3);(2,0);(3,3);(4,1);(5,1);(6,2);(7,3);(8,2);(9,0)]
              [(0, true); (1, false); (2, true)].
Proof.
  econstructor. repeat econstructor. Focus 2. simpl. auto.
  eapply thirdSAT. simpl. right. right. left. auto. constructor. simpl. 
  auto. constructor. 
Qed. 

(*colors assigned to each of the xi's are unique*)
Inductive uniqueGraphEnv S : list (vvar * colors) -> Prop :=
|rConsUnique : forall (x:vvar) (y y' y'':colors) l, 
                 uniqueGraphEnv (Add colors S y'') l ->
                 uniqueGraphEnv S ((x,y)::(x+1,y')::(x+2,y'')::l)
|rNilUnique : uniqueGraphEnv S nil. 

(*Set addition commutes (probably defined elsewhere in the standard library)*)
Theorem AddComm : forall (U:Type) S i i', Add U (Add U S i) i' = Add U (Add U S i') i. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split; intros. 
  {inv H. inv H0. constructor. constructor. auto. inv H. unfold Add. 
   apply Union_intror. constructor. inv H0. constructor. unfold Add. 
   apply Union_intror. constructor. }
  {inv H. inv H0. constructor. constructor. auto. inv H. unfold Add. 
   apply Union_intror. constructor. inv H0. constructor. unfold Add. 
   apply Union_intror. constructor. }
Qed. 

Theorem setVerticesUnique : forall Gamma eta eta' C S i, 
                        setVertices Gamma C i eta' eta -> 
                        (forall x, Ensembles.In _ S x -> x <= i) ->
                        uniqueGraphEnv S eta'. 
Proof.
  intros. generalize dependent S. induction H; intros.  
  {constructor. eapply IHsetVertices. intros. inv H2. apply H1 in H3. 
   omega. inv H3. omega. }
  {constructor. eapply IHsetVertices. intros. inv H2. apply H1 in H3. 
   omega. inv H3. omega. }
  {constructor. }
Qed. 


(*a valid graph environment assigns unique colors to each of the xs*)
Theorem validUnique : forall Gamma eta eta' C S i F, 
                        valid Gamma C F eta' eta -> 
                        (forall x, Ensembles.In _ S x -> x >= i) ->
                        uniqueGraphEnv S eta'. 
Proof.
  intros. inv H. apply setVerticesUnique with (S := Empty_set _) in H1. 
  Focus 2. intros. inv H. 


 generalize dependent S. induction H; intros.
  {constructor. eapply IHvalid. intros. inv H3. apply H2 in H4. omega. inv H4. 
   omega. }
  {constructor. eapply IHvalid. intros. inv H3. apply H2 in H4. omega. inv H4. 
   omega. }
  {constructor. }
Qed. 

Ltac copy H := 
  match type of H with
      |?x => assert(x) by auto 
  end. 

Inductive uniqueLockstep {a b c d : Type} S1 S2 S3 S4 : list (a*b*c*d) -> Prop :=
|uniqueLSCons : forall x1 x2 x3 x4 l, 
                  uniqueLockstep (Add a S1 x1) (Add b S2 x2) (Add c S3 x3)
                                 (Add d S4 x4) l -> ~ Ensembles.In _ S1 x1 ->
                  ~ Ensembles.In _ S2 x2 -> ~ Ensembles.In _ S3 x3 ->
                  ~ Ensembles.In _ S4 x4 ->
                  uniqueLockstep S1 S2 S3 S4 ((x1,x2,x3,x4)::l)
|uniqueLSNil : uniqueLockstep S1 S2 S3 S4 nil. 

Theorem InLSUnique : forall (A B C D:Type) Gamma S1 S2 S3 S4 u v v' x u1 v1 v1' x1, 
                       Ensembles.In A S1 u -> Ensembles.In B S2 v ->
                       Ensembles.In C S3 v' -> Ensembles.In D S4 x ->
                       In (u1,v1,v1',x1) Gamma -> uniqueLockstep S1 S2 S3 S4 Gamma -> 
                       u <> u1 /\ v <> v1 /\ v' <> v1' /\ x <> x1. 
Proof.
  induction Gamma; intros. 
  {inv H3. }
  {copy H3. inv H3. 
   {inv H5. inv H4. split. intros c; subst; contradiction. 
    split. intros c; subst; contradiction. split; intros c; subst; contradiction. 
    inv H4. eapply IHGamma. Focus 6. eauto. constructor. auto. 
    constructor. auto. constructor. auto. constructor. auto. auto. }
   {inv H5. inv H4. split. intros c. subst. contradiction. 
    split. intros c; subst. contradiction. split; intros c; subst; contradiction. 
    inv H4. eapply IHGamma. Focus 6. eauto. constructor. auto. constructor. auto. 
    constructor. auto. constructor. auto. auto. }
  }
Qed. 

Theorem uniqueLSNeq : forall Gamma (u u1:bvar) (v v' x v1 v1' x1:vvar) S1 S2 S3 S4, 
                        In (u,v,v',x) Gamma -> In (u1,v1,v1',x1) Gamma ->
                        uniqueLockstep S1 S2 S3 S4 Gamma -> u <> u1 ->
                        v <> v1 /\ v' <> v1' /\ x <> x1. 
Proof.
  induction Gamma; intros. 
  {inv H. }
  {simpl in *. inv H. 
   {inv H0. 
    {inv H. exfalso. apply H2. auto. }
    {inv H1. eapply InLSUnique in H7; eauto. Focus 2. unfold Add. apply Union_intror. 
     constructor. Focus 2. apply Union_intror. constructor. Focus 2. 
     apply Union_intror. constructor. Focus 2. apply Union_intror. constructor. 
     invertHyp. eauto. }
   }
   {inv H0. 
    {inv H1. eapply InLSUnique in H7; eauto. Focus 2. apply Union_intror.
     constructor. Focus 2. apply Union_intror. constructor. Focus 2. 
     apply Union_intror. constructor. Focus 2. apply Union_intror. constructor. 
     invertHyp. auto. }
    {inv H1. eapply IHGamma. Focus 3. eauto. eauto. eauto. auto. }
   }
  }
Qed.
 
Theorem InValid : forall u C Gamma i eta eta', 
                    valid Gamma C i eta' eta -> In (u,3*u,3*u+1,3*u+2) Gamma -> 
                    exists c, In (3*u+2,c) eta' /\ c <= C. 
Proof.
  intros. induction H. 
  {inv H0. 
   {inv H3. econstructor. simpl. auto. }
   {eapply IHvalid in H3. invertHyp. exists x. split; simpl; auto. }
  }
  {inv H0. 
   {inv H3. econstructor. simpl. auto. }
   {eapply IHvalid in H3. invertHyp. exists x. split; simpl; auto. }
  }
  {inv H0. }
Qed. 

Theorem LSUniqueSubset : forall A B C D a b c d S1 S2 S3 S4 Gamma, 
                           uniqueLockstep (Add A S1 a) (Add B S2 b) 
                                          (Add C S3 c) (Add D S4 d) Gamma ->
                           uniqueLockstep S1 S2 S3 S4 Gamma. 
Proof.
  intros. dependent induction H. 
  {constructor. eapply IHuniqueLockstep; auto; try solve[rewrite AddComm; auto]. 
   intros Contr. apply H0. constructor. auto. intros x. apply H1. constructor. auto. 
   intros x. apply H2. constructor. auto. intros x. apply H3. constructor. auto. }
  {constructor. }
Qed. 
 
Require Export Coq.Logic.Classical_Prop. 

Theorem notDistr : forall A B, ~(A \/ B) <-> ~ A /\ ~ B. 
Proof.
  intros. split; intros. 
  {unfold not in H. split. intros c. apply H. auto. intros c. apply H; auto. }
  {unfold not in H. invertHyp. intros c. inv c. auto. auto. }
Qed. 

Theorem genericUniqueNotIn : forall A B S (f:A -> B) (u:A) Delta,
                               Ensembles.In _ S (f u) -> 
                               genericUnique S f Delta ->  ~ In u Delta. 
Proof.
  intros. induction H0. 
  {assert(u=hd \/ u <> hd). apply classic. inv H2. 
   {contradiction. }
   {simpl. rewrite notDistr. split. auto. apply IHgenericUnique. constructor. auto. }
  }
  {intros c. auto. }
Qed. 

Theorem genericUniqueSubset : forall A B (f:A -> B) U u Delta, 
                                genericUnique (Add B U u) f Delta ->
                                genericUnique U f Delta. 
Proof.
  intros. dependent induction H. 
  {subst. constructor. eapply IHgenericUnique. rewrite AddComm. auto. 
   intros c. apply H0. constructor. auto. }
  {constructor. }
Qed. 

Ltac invertTupEq := 
  match goal with
      |H:(?x1,?x2) = (?y1,?y2) |- _ => inv H; try invertTupEq
      |H:(?x1,?x2,?x3) = (?y1,?y2,?y3) |- _ => inv H; try invertTupEq
      |H:(?x1,?x2,?x3,?x4) = (?y1,?y2,?y3,?y4) |- _ => inv H; try invertTupEq
  end. 

Ltac invUnique :=
  match goal with
      |H:uniqueLockstep ?S1 ?s2 ?s3 ?s4 (?x::?y) |- _ => inv H; try invUnique
      |H:genericUnique ?U ?f (?x::?y) |- _ => inv H; try invUnique
  end. 

Theorem ltValid : forall Gamma eta' eta c u C j U S1 S2 S3 S4, 
              valid Gamma C j eta' eta -> uniqueLockstep S1 S2 S3 S4 Gamma ->
              genericUnique U (fun a=>match a with (x,y) => x end) eta' ->
              In (u,3*u,3*u+1,3*u+2) Gamma -> In (3*u+2,c) eta' -> c <= j. 
Proof.
  intros. genDeps {{ c; u; U; S1; S2; S3; S4 }}. induction H; intros. 
  {destruct (eq_nat_dec u u0). 
   {subst. inv H4. 
    {inv H5. invertTupEq. omega. inv H4. invertTupEq. omega. inv H5. invertTupEq. omega. 
     assert(~ In (3 * S i + 2, c) eta'). invUnique. 
     eapply genericUniqueNotIn. Focus 2. eauto. apply Union_intror.
     constructor. contradiction. }
    {invUnique. eapply InLSUnique in H10; try solve[apply Union_intror; constructor]. 
     Focus 2. eauto. invertHyp. exfalso. apply H2. auto. }
   }
   {inv H4. invertTupEq. omega. inv H5. invertTupEq. omega. inv H1. invertTupEq. omega. 
    inv H4. invertTupEq. omega. invUnique. eapply IHvalid in H10; eauto. }
  }
  { destruct (eq_nat_dec u u0). 
   {subst. inv H4. 
    {inv H5. invertTupEq. omega. inv H4. invertTupEq. omega. inv H5. invertTupEq. omega. 
     assert(~ In (3 * S i + 2, c) eta'). invUnique. 
     eapply genericUniqueNotIn. Focus 2. eauto. apply Union_intror.
     constructor. contradiction. }
    {invUnique. eapply InLSUnique in H10; try solve[apply Union_intror; constructor]. 
     Focus 2. eauto. invertHyp. exfalso. apply H2. auto. }
   }
   {inv H4. invertTupEq. omega. inv H5. invertTupEq. omega. inv H1. invertTupEq. omega. 
    inv H4. invertTupEq. omega. invUnique. eapply IHvalid in H10; eauto. }
  }
  {inv H3. }
Qed. 


