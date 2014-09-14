Require Import ThreeSatReduction. 

Inductive genericUnique {A B :Type} (U:Ensemble B) (f:A -> B) : list A -> Prop :=
|uniqueCons : forall hd tl, genericUnique (Add B U (f hd)) f tl ->
                       ~ Ensembles.In _ U (f hd) -> genericUnique U f (hd::tl)
|uniqueNil : genericUnique U f nil. 

Inductive valid : list (bvar*vvar*vvar*vvar) -> nat -> nat ->
                        list (vvar * colors) -> list (bvar * bool) -> Prop :=
|validF : forall u (v v' : vvar) x eta eta' C i Gamma, 
            valid Gamma C (S i) eta' eta -> i <= C -> 
            valid ((u,v,v',x)::Gamma) C i ((v,i)::(v',0)::(x,i)::eta')((u,true)::eta)
|validT : forall u (v v' : vvar) x eta eta' i C Gamma, 
            valid Gamma C (S i) eta' eta -> i <= C -> 
            valid ((u,v,v',x)::Gamma) C i ((v,0)::(v',i)::(x,i)::eta') ((u, false)::eta)
|validNil : forall C i, valid nil C i nil nil.

Inductive uniqueGraphEnv S : list (vvar * colors) -> Prop :=
|rConsUnique : forall (x x' x'':vvar) (y y' y'':colors) l, 
                 uniqueGraphEnv (Add colors S y'') l ->
                 uniqueGraphEnv S ((x,y)::(x',y')::(x'',y'')::l)
|rNilUnique : uniqueGraphEnv S nil. 

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

Theorem validUnique' : forall Gamma eta eta' C i U, 
                        valid Gamma C (S i) eta' eta -> uniqueGraphEnv U eta' -> 
                        uniqueGraphEnv (Add colors U i) eta'.
Proof.
  intros. generalize dependent U. induction H; intros. 
  {constructor. rewrite AddComm. apply IHvalid. inv H1. auto. }
  {inv H1. constructor. rewrite AddComm. eauto. }
  {constructor. }
Qed. 

Theorem validUnique : forall Gamma eta eta' C S i, 
                        valid Gamma C i eta' eta -> 
                        uniqueGraphEnv S eta'. 
Proof.
  intros. induction H. 
  {constructor. eapply validUnique'; eauto. }
  {constructor. eapply validUnique'; eauto. }
  {constructor. }
Qed. 
        
Inductive domainsEq : list bvar -> list (bvar*vvar*vvar*vvar) -> Prop :=
|eqCons : forall x a b c l l', domainsEq l l' -> domainsEq (x::l) ((x,a,b,c)::l')
|eqNil : domainsEq nil nil. 

(*asserts that Delta is a postfix of Domain(Gamma)*)
Inductive domainPostfix : list bvar -> list (bvar*vvar*vvar*vvar) -> Prop :=
|postfixCons : forall l l' hd, domainPostfix l l' -> domainPostfix l (hd::l')
|postfixEq : forall l l', domainsEq l l' -> domainPostfix l l'. 

Theorem postfixShorter : forall u Delta Gamma, domainPostfix (u::Delta) Gamma -> domainPostfix Delta Gamma. 
Proof.
  intros. remember(u::Delta). induction H. 
  {constructor. auto. }{subst. inv H. apply postfixCons. apply postfixEq. auto. }
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
Theorem InValid : forall u v v' x C Gamma i eta eta', 
                    valid Gamma C i eta' eta -> In (u,v,v',x) Gamma -> 
                    exists c, In (x,c) eta' /\ c <= C. 
Proof.
  intros. induction H. 
  {inv H0. 
   {inv H2. simpl. exists i. split. auto. auto. }
   {eapply IHvalid in H2. invertHyp. exists x1. split. simpl. 
    right. eauto. auto. }
  }
  {inv H0. 
   {inv H2. simpl. exists i. split. auto. auto. }
   {eapply IHvalid in H2. invertHyp. exists x1. split. simpl. 
    right. eauto. auto. }
  }
  {inv H0. }
Qed. 

Require Import Coq.Program.Equality. 

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

Theorem ltValid : forall Gamma eta' eta c u v S v' x C j, 
              genericUnique S (fun arg => match arg with (x,_) => x end) eta' ->
              valid Gamma C j eta' eta -> 
              In (u,v,v',x) Gamma -> In (x,c) eta' -> c >= j. 
Proof.
  intros. genDeps {{ c; x; u; v; v' }}. induction H0; intros. 
  {inv H2. 
   {inv H4. inv H. inv H5. inv H4. inv H3. inv H. auto. inv H. 
    inv H2. exfalso. apply H8. apply Union_intror. constructor. inv H2. 
    inv H. auto. assert (~ In (x0,c) eta'). eapply genericUniqueNotIn. 
    Focus 2. eauto. simpl. apply Union_intror. constructor. contradiction. }
   {inv H3. inv H2. auto. inv H2. inv H3. inv H. inv H5. inv H3. 
    Admitted. 



Theorem edgesNeq : forall eta' eta Gamma C i u v v' x u1 v1 v1' x1 S1 S2 S3 S4, 
                     u <> u1 -> In (u,v,v',x) Gamma -> In (u1,v1,v1',x1) Gamma ->
                     valid Gamma C i eta' eta -> uniqueLockstep S1 S2 S3 S4 Gamma ->
                     exists c1 c2, In (x,c1) eta' /\ In (x1, c2) eta' /\ c1 <> c2 /\
                              c1 <= C /\ c2 <= C. 
Proof.
  intros. genDeps {{ u;v;v';x;u1;v1;v1';x1 }}. induction H2; intros.
  {inv H1. 
   {inv H5. inv H4. 
    {inv H1. exfalso. apply H0; auto. }
    {inv H3. copy H1. eapply InValid in H1; eauto. invertHyp. 
     exists x. exists i. split. simpl. auto. split. simpl. auto. split; auto. 
     eapply ltValid in H2; eauto. omega. }
   }
   {inv H4.
    {inv H1. inv H3. exists i. copy H5. eapply InValid in H5; eauto. invertHyp. 
     exists x. split; simpl; auto. split. auto. split; auto. eapply ltValid in H2; eauto. 
     omega. }
    {inv H3. eapply IHvalid in H5; eauto. invertHyp. exists x3. exists x2. simpl. 
     split; auto. eapply LSUniqueSubset; eauto. }
   }
  }
  {inv H1. 
   {inv H5. inv H4. 
    {inv H1. exfalso. apply H0; auto. }
    {inv H3. copy H1. eapply InValid in H1; eauto. invertHyp. 
     exists x. exists i. split. simpl. auto. split. simpl. auto. split; auto. admit. }
   }
   {inv H4.
    {inv H1. inv H3. eapply InValid in H5; eauto. invertHyp. exists i. exists x. 
     split. simpl; auto. split. simpl; auto. split ;auto. 

 admit. }
    {inv H3. eapply IHvalid in H5; eauto. invertHyp. exists x3. exists x2. simpl. 
     split; auto. eapply LSUniqueSubset; eauto. }
   }
  }
  {inv H0. }
Qed. 

Theorem connectXColorable : forall Gamma Delta G C eta eta' u v v' x S1 S2 S3 S4, 
                              uniqueLockstep S1 S2 S3 S4 Gamma -> 
                              ~In u Delta -> valid Gamma C 1 eta' eta -> In (u,v,v',x) Gamma ->
                              connectX Gamma Delta x G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ u; v; v'; eta; C; eta'}}. induction H3; intros. 
  {constructor. }
  {copy H1. eapply validUnique with (S := Empty_set _) in H5. 
   destruct(eq_nat_dec u u0). 
   {subst. simpl in H2. exfalso. apply H2. auto. }
   {copy H1. eapply edgesNeq in H1; eauto. invertHyp. econstructor; eauto.
    eapply IHconnectX; eauto. intros c. apply H2. simpl. right. auto. }
  }
Qed. 

Theorem cliqueColorable : forall Gamma eta Delta C G eta' S1 S2 S3 S4 S5, 
                            valid Gamma C 1 eta' eta -> domainPostfix Delta Gamma -> 
                            uniqueLockstep S1 S2 S3 S4 Gamma ->
                            genericUnique S5 (fun x => x) Delta -> 
                            clique Gamma Delta G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ eta; C }}. induction H3; intros; auto. 
  {constructor. eapply IHclique; eauto. inv H0. eapply postfixShorter. constructor. 
   eauto. inv H6. constructor. apply postfixEq. auto. inv H2. 
   eapply genericUniqueSubset; eauto. eapply connectXColorable; eauto. inv H2. 
   eapply genericUniqueNotIn. Focus 2. eauto. simpl. apply Union_intror. constructor. 
  }
Qed. 

Theorem KColorNPC : forall Gamma Delta K F C eta C' G eta',
                      domainPostfix Delta Gamma -> reduce Gamma Delta K F C C' G -> 
                      valid Gamma C' 1 eta' eta ->
                      (stackSAT eta K /\ SAT' eta F <-> coloring eta' G C').
Proof.
  intros. split; intros. 
  {generalize dependent eta'. induction H0; intros. 
   {invertHyp. inv H4. apply IHreduce; auto. simpl. auto. }
   {constructor. admit. constructor.
    eapply cliqueColorable with (Gamma := Gamma)(S := Empty_set colors)(Delta := Delta); auto. 




Theorem KColorNPC' : forall Gamma Delta K F C eta n C' G eta',
                      Reduce F n ->
                      (SAT n F <-> setVarsG (3 * n) eta' G C').
Proof.


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









