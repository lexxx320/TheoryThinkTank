(*This file contains the proof that a clique generated from the clique 
**inductive type is colorable assuming each vertex is uniquely colored
**as specified by the setVertices relation*)
Require Export ThreeSatReduction.  

(*connecting x_i to each x_j when i <> j preserves colorability*)
Theorem connectXColorable : forall Gamma Delta G C eta eta' u, 
                              ~In u Delta -> setVertices Gamma C 0 eta' eta -> In (u,3*u,3*u+1,3*u+2) Gamma ->
                              connectX Gamma Delta (3*u+2) G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ eta; C; eta'}}. remember (3*u+2). induction H2; intros. 
  {constructor. } 
  {subst. destruct(eq_nat_dec u u0). 
   {subst. exfalso. apply H. simpl. auto. }
   {copy H3. eapply XMapsToU in H0; eauto. copy H1. eapply XMapsToU in H1; eauto.
    invertHyp. econstructor; eauto. omega. omega. eapply IHconnectX; eauto. intros c. 
    apply H. simpl. auto. }
  }
Qed. 

Theorem cliqueColorable : forall Gamma eta Delta C G eta' U, 
                            setVertices Gamma C 0 eta' eta -> 
                            unique U Delta -> 
                            clique Gamma Delta G -> coloring eta' G C. 
Proof.
  intros. genDeps {{ eta; C; U }}. induction H1; intros; auto. 
  {constructor. eapply IHclique; eauto. inv H0. constructor. inv H2. eauto. 
   eapply connectXColorable; eauto. inv H2. eapply uniqueNotIn; eauto. 
   apply Union_intror. constructor. }
Qed. 
