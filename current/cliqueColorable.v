Require Export ThreeSatReduction.  

Theorem edgesNeq : forall eta' eta Gamma C i u u1, 
                     u <> u1 -> In (u,3*u,3*u+1,3*u+2) Gamma -> In (u1,3*u1,3*u1+1,3*u1+2) Gamma ->
                     setVertices Gamma C i eta' eta -> 
                     exists c1 c2, In (3*u+2,c1) eta' /\ In (3*u1+2, c2) eta' /\ c1 <> c2 /\
                              c1 <= C /\ c2 <= C. 
Proof.
  intros. genDeps {{ u;u1 }}. induction H2; intros.
  {inCons. 
   {inCons. invertTupEq. omega. invertTupEq. copy H2. eapply InSetVertices in H2; eauto. 
    invertHyp. eapply geSetVertices in H1; eauto. exists u0. exists x. split. simpl. 
    auto. split. simpl. auto. split; auto. omega. split; auto. omega. }
   {inCons. invertTupEq. copy H2. eapply InSetVertices in H2; eauto. 
    invertHyp. eapply geSetVertices in H1; eauto. exists x. exists u1. split. simpl. auto. split. 
    simpl. auto. split. omega. split; auto. omega. eapply IHsetVertices in H0; eauto. 
    invertHyp. exists x. exists x0. split. simpl. auto. split. simpl. auto. auto. }
  }
  {inCons. 
   {inCons. invertTupEq. omega. invertTupEq. copy H2. eapply InSetVertices in H2; eauto. 
    invertHyp. eapply geSetVertices in H1; eauto. exists u0. exists x. split. simpl. 
    auto. split. simpl. auto. split; auto. omega. split; auto. omega. }
   {inCons. invertTupEq. copy H2. eapply InSetVertices in H2; eauto. 
    invertHyp. eapply geSetVertices in H1; eauto. exists x. exists u1. split. simpl. auto. split. 
    simpl. auto. split. omega. split; auto. omega. eapply IHsetVertices in H0; eauto. 
    invertHyp. exists x. exists x0. split. simpl. auto. split. simpl. auto. auto. }
  }
  {inv H0. }
Qed. 

Theorem connectXColorable : forall Gamma Delta G C eta eta' u, 
                              ~In u Delta -> setVertices Gamma C 0 eta' eta -> In (u,3*u,3*u+1,3*u+2) Gamma ->
                              connectX Gamma Delta (3*u+2) G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ eta; C; eta'}}. remember (3*u+2). induction H2; intros. 
  {constructor. } 
  {subst. destruct(eq_nat_dec u u0). 
   {subst. exfalso. apply H. simpl. auto. }
   {copy H3. eapply edgesNeq in H3; eauto. invertHyp. econstructor; eauto.
    eapply IHconnectX; eauto. intros c. apply H. simpl. right. auto. }
  }
Qed. 
 
Theorem cliqueColorable : forall Gamma eta Delta C G eta' S5, 
                            setVertices Gamma C 0 eta' eta -> 
                            genericUnique S5 (fun x => x) Delta -> 
                            clique Gamma Delta G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ eta; C }}. induction H1; intros; auto. 
  {constructor. eapply IHclique; eauto. inv H0. eapply genericUniqueSubset; eauto. 
   eapply connectXColorable; eauto. inv H0. eapply genericUniqueNotIn. 
   Focus 2. eauto. simpl. apply Union_intror. constructor. }
Qed. 
