(*vars_to_clique attaches each v_i and v_i' to x_i.  If in the boolean formula,
**u_i is set to true in a satisfiable environment, then v_i gets assigned the color u_i
**and v_i' gets assigned the color C*)
Require Export ThreeSatReduction. 

(*attaching v_i to x_j for i <> j preserves coloring*)
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

(*attaching v_i' to x_j for i <> j preserves coloring*)
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

(*attaching x_i to v_i and v_i' for i <> j preserves coloring*)
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

Theorem varsToCliqueColorable : forall Gamma eta Delta C G eta' U, 
                            setVertices Gamma C 0 eta' eta -> 
                            unique U Delta -> 
                            vars_to_clique Gamma Delta G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ U; eta'; eta; C }}. induction H1; intros. 
  {constructor. }
  {inv H5. constructor. eapply IHvars_to_clique; eauto. constructor. 
   eapply connectXColorable; eauto. eapply uniqueNotIn; eauto. apply Union_intror. 
   constructor. constructor. eapply connectXColorable'; eauto. 
   eapply uniqueNotIn; eauto. apply Union_intror. constructor. 
   eapply connectVColorable; eauto. eapply uniqueNotIn; eauto.  
   apply Union_intror. constructor. }
Qed. 


