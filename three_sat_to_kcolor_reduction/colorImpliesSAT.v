(*This file contains the proof that if we reduce a formula F to a graph G, 
**and G is colorable, then F is satisfiable under valid environments*)
Require Import ThreeSatReduction.  

(*collect the free variables of a graph*)
Fixpoint graphFVs G :=
  match G with
    |emptyGraph => []
    |newEdge u v G => u::v::graphFVs G
    |gunion G1 G2 => graphFVs G1 ++ graphFVs G2
  end.

(*solve a goal of the form In ?x ?y*)
Ltac solveIn :=
  match goal with
      | |- In ?x (?a ++ ?b) => rewrite in_app_iff; 
                            solve[left; solveIn|right; solveIn]
      | |- In ?a ?b \/ In ?c ?d => simpl in *; solve[left; solveIn | right; solveIn]
      | |- In ?a (?b::?c) => simpl; solve[left; auto|right; solveIn]
      | |- _ => eauto
  end. 

(*color a graph with a smaller environment if the part being removed
**does not occur free in the graph being colored*)
Theorem colorStrengthening : forall eta1 eta2 i c j K Gamma C eta G,
                               setVertices Gamma C 0 eta1 eta ->
                               setCs eta1 i K eta2 eta ->
                               coloring (eta1++(j,c)::eta2) G C ->
                               ~ In j (graphFVs G) ->
                               coloring (eta1++eta2) G C.
Proof.
  intros. remember (eta1++(j,c)::eta2). induction H1. 
  {constructor. }
  {simpl in H2. subst. rewrite in_app_iff in H1. rewrite in_app_iff in H3. 
   inv H1; inv H3.
   {econstructor; try solveIn; try omega. eapply IHcoloring; eauto. }
   {econstructor; try solveIn; try omega. simpl in H1. inv H1. invertTupEq. 
    exfalso. apply H2. auto. solveIn. apply IHcoloring; auto. }
   {simpl in H8. inv H8. invertTupEq. exfalso. apply H2. auto. 
    econstructor; try solveIn. apply IHcoloring; auto. }
   {simpl in *. inv H8. invertTupEq. exfalso. apply H2. auto. inv H1. invertTupEq. 
    exfalso. apply H2. auto. econstructor; try solveIn. apply IHcoloring; auto. }
  }
  {constructor. apply IHcoloring1; auto. intros contra. apply H2. simpl. 
   solveIn. apply IHcoloring2; auto. intros contra. apply H2. simpl. solveIn. }
Qed. 

Theorem notInDistribute : forall (A:Type) (x:A) L1 L2, ~ In x L1 -> ~ In x L2 ->
                                                  ~ In x (L1++L2). 
Proof. intros. rewrite in_app_iff. rewrite notDistr. auto. 
Qed. 

(*If a mapping from u_i to its vertex variables is in Gamma, then x_i is less than the length of Gamma + i*)
Theorem inGammaLT : forall Gamma C i eta eta' u, In (u,3*u,3*u+1,3*u+2) Gamma -> setVertices Gamma C i eta' eta ->
                                         3 * u + 2 < 3 * (length Gamma + i). 
Proof.
  intros. induction H0. 
  {inv H. 
   {invertTupEq. simpl. omega. }
   {eapply IHsetVertices in H2. simpl. omega. }
  }
  {inv H. 
   {invertTupEq. simpl. omega. }
   {eapply IHsetVertices in H2. simpl. omega. }
  }
  {inv H. }
Qed. 

(*if j is less than the convert_base index, then j is not in the free variables of G*)
Theorem notInConvertBase : forall Gamma Delta i G j eta C eta',
                             setVertices Gamma C 0 eta' eta -> j < i -> j >= 3 * length Gamma ->
                             convert_base Gamma Delta i G ->
                             ~ In j (graphFVs G). 
Proof.
  intros. induction H2. 
  {intros c. inv c. } 
  {simpl. repeat rewrite notDistr; repeat split; try omega. 
   eapply inGammaLT in H2; eauto; simpl in *. repeat rewrite plus_0_r in *. 
   apply lt_le_trans with(p:=j) in H2; auto. omega. 
   eapply inGammaLT in H2; eauto. simpl in *. repeat rewrite plus_0_r in *. 
   apply lt_le_trans with(p:=j) in H2; auto. omega. auto. }
Qed. 

(*if j is less than the convStack index and greater than everything in Gamma, then it
**is not in the free variables of G*)
Theorem notInFV : forall Gamma C eta1 eta Delta G j K i eta2, 
                    setVertices Gamma C 0 eta1 eta -> setCs eta1 i K eta2 eta ->
                    j >= 3 * length Gamma -> j < i -> convStack i Gamma Delta K G -> ~ In j (graphFVs G). 
Proof.
  intros. genDeps {{ j; eta; eta1; eta2 }}. induction H3; intros.
  {intros c. inv c. }
  {simpl. apply notInDistribute. inv H1; eapply IHconvStack; eauto;
   rewrite plus_comm; eauto. destruct F. destruct p. inv H. simpl. 
   destruct e1. destruct e2. destruct e3. simpl.
   repeat rewrite notDistr; repeat split. inv H12; omega. eapply inGammaLT in H8; eauto. 
   inv H12. simpl in *. repeat rewrite plus_0_r in H8. rewrite plus_0_r in H2. 
   assert(3*u+2 < j). simpl. rewrite plus_0_r. eapply lt_le_trans with(p:=j) in H8. Focus 2. 
   auto. auto. omega. simpl in *. eapply lt_le_trans with (p:=j) in H8. Focus 2. 
   repeat rewrite plus_0_r in *. auto. omega. inv H18; omega. eapply inGammaLT in H9; eauto. inv H18; 
   eapply lt_le_trans with (p:=j) in H9; simpl in *; repeat rewrite plus_0_r in *; auto; 
   omega. inv H20; omega. eapply inGammaLT in H10; eauto.
   inv H20; eapply lt_le_trans with (p:=j) in H10; simpl in *; repeat rewrite plus_0_r in *; auto; omega. 
   eapply notInConvertBase; eauto. }
Qed. 

(*If F reduces to G and G is colorable, then F is satisfiable*)
Theorem colorImpliesSAT : forall Gamma C eta eta' i U eta'' Delta F G,
                            setVertices Gamma C 0 eta' eta -> setCs eta' i F eta'' eta ->
                            coloring (eta'++eta'') G C -> i >= 3 * length Gamma ->
                            unique U Delta -> 
                            convStack i Gamma Delta F G -> SAT' eta F. 
Proof.
  intros. genDeps {{ U; eta; eta'; eta''; C }}. induction H4; intros. 
  {constructor. } 
  {destruct F. destruct p. inv H3. 
   {inv H13. 
    {constructor. left. constructor. auto. eapply IHconvStack. omega. Focus 3.
     rewrite plus_comm. eauto. Focus 3. eauto. Focus 2. eauto. 
     eapply colorStrengthening; eauto. inv H1. eauto. eapply notInFV; eauto.
     rewrite plus_comm in H4. eauto. }
    {constructor. left. constructor. auto. eapply IHconvStack. Focus 4.
     rewrite plus_comm. eauto. Focus 3. eauto. Focus 2. eauto. 
     eapply colorStrengthening; eauto. inv H1. eauto. eapply notInFV; eauto.
     rewrite plus_comm in H4. eauto. omega. eauto. }
   }
   {inv H13. 
    {constructor. right. left. constructor. auto. eapply IHconvStack. Focus 4.
     rewrite plus_comm. eauto. Focus 3. eauto. Focus 2. eauto.  
     eapply colorStrengthening; eauto. inv H1. eauto. eapply notInFV; eauto.
     rewrite plus_comm in H4. eauto. omega. eauto. }
    {constructor. right. left. constructor. auto. eapply IHconvStack. Focus 4.
     rewrite plus_comm. eauto. omega. Focus 3. eauto. Focus 2. eauto. 
     eapply colorStrengthening; eauto. inv H1. eauto. eapply notInFV; eauto.
     rewrite plus_comm in H4. eauto. }
   }
   {inv H13. 
    {constructor. right. right. constructor. auto. eapply IHconvStack. Focus 4.
     rewrite plus_comm. eauto. Focus 3. eauto. Focus 3. eauto. omega. 
      eapply colorStrengthening; eauto. inv H1. eauto. eapply notInFV; eauto.
     rewrite plus_comm in H4. eauto. }
    {constructor. right. right. constructor. auto. eapply IHconvStack. Focus 4.
     rewrite plus_comm. eauto. Focus 4. eauto. Focus 3. eauto. omega. 
      eapply colorStrengthening; eauto. inv H1. eauto. eapply notInFV; eauto.
     rewrite plus_comm in H4. eauto. }
   }
  }
Qed. 


