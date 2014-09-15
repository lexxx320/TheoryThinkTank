Require Export ThreeSatReduction.  

Theorem edgesNeq : forall eta' eta Gamma C i u U u1 S1 S2 S3 S4, 
                     u <> u1 -> In (u,3*u,3*u+1,3*u+2) Gamma -> In (u1,3*u1,3*u1+1,3*u1+2) Gamma ->
                     valid Gamma C i eta' eta -> uniqueLockstep S1 S2 S3 S4 Gamma ->
                     genericUnique U (fun a=>match a with (x,y) => x end) eta' ->
                     exists c1 c2, In (3*u+2,c1) eta' /\ In (3*u1+2, c2) eta' /\ c1 <> c2 /\
                              c1 <= C /\ c2 <= C. 
Proof.
  intros. genDeps {{ u;u1;S1;S2;S3;S4;U }}. induction H2; intros.
  {inv H1.  
   {inv H6. 
    {invertTupEq. omega. }
    {invertTupEq. inv H3. copy H2. eapply InValid in H2; eauto. invertHyp. 
     econstructor. econstructor. split. simpl. repeat right. eauto. split. 
     simpl. auto. invUnique. eapply ltValid in H13; eauto.
     split. omega. split; auto. }
   }
   {inv H6. 
    {invUnique. invertTupEq. exists (S i). copy H2. eapply InValid in H2; eauto. invertHyp. exists x. 
     split; simpl; auto. split. auto. split; auto. eapply ltValid in H2; eauto. omega. }
    {invUnique. eapply IHvalid in H7; eauto. invertHyp. exists x0. exists x. simpl. split; auto. }
   }
  }
  {inv H1.  
   {inv H6. 
    {invertTupEq. omega. }
    {invertTupEq. inv H3. copy H2. eapply InValid in H2; eauto. invertHyp. 
     econstructor. econstructor. split. simpl. repeat right. eauto. split. 
     simpl. auto. invUnique. eapply ltValid in H13; eauto.
     split. omega. split; auto. }
   }
   {inv H6. 
    {invUnique. invertTupEq. exists (S i). copy H2. eapply InValid in H2; eauto. invertHyp. exists x. 
     split; simpl; auto. split. auto. split; auto. eapply ltValid in H2; eauto. omega. }
    {invUnique. eapply IHvalid in H7; eauto. invertHyp. exists x0. exists x. simpl. split; auto. }
   }
  }
  {inv H0. }
Qed. 

Theorem connectXColorable : forall Gamma Delta G C eta eta' U u S1 S2 S3 S4, 
                              uniqueLockstep S1 S2 S3 S4 Gamma -> 
                              ~In u Delta -> valid Gamma C 1 eta' eta -> In (u,3*u,3*u+1,3*u+2) Gamma ->
                              genericUnique U (fun a=>match a with (x,y) => x end) eta' ->
                              connectX Gamma Delta (3*u+2) G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ eta; C; eta'}}. remember (3*u+2). induction H4; intros. 
  {constructor. } 
  {subst. copy H5. eapply validUnique with (S := Empty_set _) in H5. 
   destruct(eq_nat_dec u u0). 
   {subst. simpl in H2. exfalso. apply H0. simpl. auto. }
   {copy H6. eapply edgesNeq in H6; eauto. invertHyp. econstructor; eauto.
    eapply IHconnectX; eauto. intros c. apply H0. simpl. right. auto. }
   intros. inv H7. 
  }
Qed. 

Theorem cliqueColorable : forall Gamma eta Delta C G eta' U S1 S2 S3 S4 S5, 
                            valid Gamma C 1 eta' eta -> 
                            uniqueLockstep S1 S2 S3 S4 Gamma ->
                            genericUnique S5 (fun x => x) Delta -> 
                            genericUnique U (fun a=>match a with (x,y) => x end) eta' ->
                            clique Gamma Delta G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ eta; C; U }}. induction H3; intros; auto. 
  {constructor. eapply IHclique; eauto. inv H1. eapply genericUniqueSubset; eauto. 
   eapply connectXColorable; eauto. inv H1. eapply genericUniqueNotIn. 
   Focus 2. eauto. simpl. apply Union_intror. constructor. }
Qed. 
