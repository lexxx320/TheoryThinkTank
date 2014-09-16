Require Export ThreeSatReduction. 


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

Theorem edgesNeq : forall Gamma C eta' eta u i u0,
                     In (u,3*u,3*u+1,3*u+2) Gamma -> In (u0,3*u0,3*u0+1,3*u0+2) Gamma ->
                     setVertices Gamma C i eta' eta -> u <> u0 ->
                     exists c1 c2, In (3*u, c1) eta' /\ In (3*u0+2, c2) eta' /\
                              c1 <= C /\ c2 <= C /\ c1 <> c2. 
Proof.
  intros. genDeps {{ u; u0 }}. induction H1; intros. 
  {inCons. 
   {inCons. 
    {invertTupEq. omega. }
    {invertTupEq. exists u1. copy H1. eapply InSetVertices in H1; eauto. invertHyp. 
     exists x. split. simpl. auto. split. simpl. auto. split; auto. omega. split; auto. 
     eapply geSetVertices in H0; eauto. omega. }
   }
   {inCons. 
    {invertTupEq. eapply V_V'MapToUOrC in H4; eauto. inv H4; invertHyp.  
     {exists u1. exists u0. split; simpl; auto. split; auto. split. omega. split; auto. omega. }
     {exists C. exists u0. split. simpl. auto. split. simpl. auto. split; auto. split; omega. }
    }
    {eapply IHsetVertices in H4; eauto. invertHyp. exists x. exists x0. split. simpl. auto. 
     split. simpl. auto. split; auto. }
   }
  }
  {inCons. 
   {inCons. 
    {invertTupEq. omega. }
    {invertTupEq. exists C. copy H1. eapply XMapsToU in H1; eauto. invertHyp. exists u0. split. 
     simpl. auto. split. simpl. auto. split; auto. split; omega. }
   }
   {inCons. 
    {invertTupEq. eapply V_V'MapToUOrC in H4; eauto. inv H4. 
     {invertHyp. exists u1. exists u0. split. simpl. auto. split. simpl. auto. split; auto. 
      omega. split; auto. omega. }
     {invertHyp. exists C. exists u0. split. simpl. auto. split. simpl. auto. split; auto. split; omega. }
    }
    {eapply IHsetVertices in H4; eauto. invertHyp. exists x. exists x0. split. simpl. auto. 
     split. simpl. auto. split; auto. }
   }
  }
  {inv H. }
Qed. 

Theorem connectXColorable : forall Gamma Delta G C eta eta' u, 
                              ~In u Delta -> setVertices Gamma C 0 eta' eta -> In (u,3*u,3*u+1,3*u+2) Gamma ->
                              connectX Gamma Delta (3*u) G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ eta; C; eta'}}. remember (3*u). induction H2; intros. 
  {constructor. } 
  {subst. destruct(eq_nat_dec u u0). 
   {subst. exfalso. apply H. simpl. auto. }
   {copy H3. eapply edgesNeq in H3. Focus 2. eauto. Focus 2. eapply H0. invertHyp. 
    econstructor; eauto. eapply IHconnectX; eauto. intros c. apply H. simpl. auto.
    eauto. }
  }
Qed. 

Theorem cliqueColorable : forall Gamma eta Delta C G eta' S5, 
                            setVertices Gamma C 0 eta' eta -> 
                            genericUnique S5 (fun x => x) Delta -> 
                            vars_to_clique Gamma Delta G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ S5; eta'; eta; C }}. induction H1; intros. 
  {constructor. }
  {constructor. eapply IHvars_to_clique; eauto. inv H5. eauto. constructor. 
   eapply connectXColorable; eauto. eapply genericUniqueNotIn; eauto. Focus 2. inv H5. 
   eauto. apply Union_intror. constructor. 





asdfasdfsadf