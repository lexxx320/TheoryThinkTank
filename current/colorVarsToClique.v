Require Export ThreeSatReduction. 

Theorem connectXColorable : forall Gamma Delta G C eta eta' u, 
                              ~In u Delta -> setVertices Gamma C 0 eta' eta -> In (u,3*u,3*u+1,3*u+2) Gamma ->
                              connectX Gamma Delta (3*u) G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ eta; C; eta'}}. remember (3*u). induction H2; intros. 
  {constructor. } 
  {subst. destruct(eq_nat_dec u u0). 
   {subst. exfalso. apply H. simpl. auto. }
   {copy H3. copy H1. eapply V_V'MapToUOrC in H1; eauto. eapply XMapsToU in H0; eauto. 
    inv H1. invertHyp. econstructor; eauto. omega. omega. eapply IHconnectX; eauto. 
    intros c. apply H. simpl; auto. invertHyp. econstructor; eauto. omega. 
    omega. eapply IHconnectX; eauto. intros c. apply H. simpl; auto. }
  }
Qed. 

Theorem connectXColorable' : forall Gamma Delta G C eta eta' u, 
                              ~In u Delta -> setVertices Gamma C 0 eta' eta -> In (u,3*u,3*u+1,3*u+2) Gamma ->
                              connectX Gamma Delta (3*u+1) G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ eta; C; eta'}}. remember (3*u+1). induction H2; intros. 
  {constructor. } 
  {subst. destruct(eq_nat_dec u u0). 
   {subst. exfalso. apply H. simpl. auto. }
   {copy H3. copy H1. eapply V_V'MapToUOrC in H1; eauto. eapply XMapsToU in H0; eauto. 
    inv H1. invertHyp. econstructor; eauto. omega. omega. eapply IHconnectX; eauto. 
    intros c. apply H. simpl; auto. invertHyp. econstructor; eauto. omega. 
    omega. eapply IHconnectX; eauto. intros c. apply H. simpl; auto. }
  }
Qed. 


Theorem connectVColorable : forall Gamma Delta G C eta eta' u, 
                              ~In u Delta -> setVertices Gamma C 0 eta' eta -> In (u,3*u,3*u+1,3*u+2) Gamma ->
                              connectV Gamma Delta (3*u+2) G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ eta; C; eta'}}. remember (3*u+2). induction H2; intros. 
  {constructor. } 
  {subst. destruct(eq_nat_dec u u0). 
   {subst. exfalso. apply H. simpl. auto. }
   {copy H3. copy H1. eapply XMapsToU in H1; eauto. eapply V_V'MapToUOrC in H0; eauto. 
    inv H0. 
    {invertHyp. econstructor; eauto; try omega. econstructor; eauto; try omega. 
     eapply IHconnectV; eauto. intros contra. apply H. simpl. auto. }
    {invertHyp. econstructor; eauto; try omega. econstructor; eauto; try omega. 
     eapply IHconnectV; eauto. intros contra. apply H. simpl; auto. }
   }
  }
Qed. 

Theorem varsToCliqueColorable : forall Gamma eta Delta C G eta' S5, 
                            setVertices Gamma C 0 eta' eta -> 
                            genericUnique S5 (fun x => x) Delta -> 
                            vars_to_clique Gamma Delta G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ S5; eta'; eta; C }}. induction H1; intros. 
  {constructor. }
  {constructor. eapply IHvars_to_clique; eauto. inv H5. eauto. constructor. 
   eapply connectXColorable; eauto. eapply genericUniqueNotIn; eauto. Focus 2. inv H5. 
   eauto. apply Union_intror. constructor. constructor. eapply connectXColorable'; eauto. 
   inv H5. eapply genericUniqueNotIn. Focus 2. eauto. apply Union_intror. constructor. 
   eapply connectVColorable; eauto. inv H5. eapply genericUniqueNotIn. Focus 2. eauto. 
   apply Union_intror. constructor. }
Qed. 


