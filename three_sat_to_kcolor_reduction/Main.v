Require Import cliqueColorable.      
Require Import colorVarsToClique.  
Require Import colorConvStack. 
Require Import colorImpliesSAT. 

(*tacitic for solving set membership goals*)
Ltac inSet :=
  match goal with
      |H:Ensembles.In _ (Add _ ?x ?y) ?z |- _ => inv H
      |H:Ensembles.In _ (Singleton _ ?x) ?y |- _ => inv H
  end. 

Theorem KColorNPC : forall Gamma Delta F C eta G eta' U,
                      reduce Gamma Delta F G -> 
                      valid Gamma C F eta' eta -> unique U Delta -> 
                      (SAT' eta F <-> coloring eta' G C).
Proof. 
  intros. inv H. split; intros. 
  {constructor. 
   {inv H0. eapply convStackColorable in H2; eauto. rewrite mult_comm. auto. }
   {constructor. 
    {inv H0. eapply colorWeakening. eapply cliqueColorable; eauto. }
    {inv H0. apply colorWeakening. eapply varsToCliqueColorable; eauto. }
   }
  }
  {inv H0. inv H. inv H11. eapply colorImpliesSAT. eauto. eauto. eapply H9.
   auto. eauto. rewrite mult_comm. eauto. }
Qed. 

Theorem buildCtxtUnique : forall i Gamma Delta U, 
                            buildCtxt i = (Gamma, Delta) -> 
                            (forall x, Ensembles.In vvar U x -> S x > i) -> 
                            unique U Delta. 
Proof.
  induction i; intros.
  {inv H. constructor. } 
  {simpl in *. destruct (buildCtxt i). inv H. constructor. eapply IHi. 
   reflexivity. intros. inv H. apply H0 in H1. omega. inv H1. omega.
   intro. apply H0 in H. omega. }
Qed. 

(*TODO: we need to somehow relate n to the number of unique variables in F*)
Theorem KColorNPCTopLevel : forall Gamma Delta F n G eta eta', 
                              buildCtxt n = (Gamma, Delta) ->
                              reduce Gamma Delta F G -> valid Gamma (n+1) F eta' eta ->
                              (SAT' eta F <-> coloring eta' G (n+1)). 
Proof.
  intros. apply buildCtxtUnique with (U:=Empty_set _) in H. Focus 2. intros. 
  inv H2. eapply KColorNPC in H0; eauto. 
Qed.



