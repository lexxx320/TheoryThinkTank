Require Import cliqueColorable.     
Require Import colorVarsToClique. 
 
Ltac inSet :=
  match goal with
      |H:Ensembles.In _ (Add _ ?x ?y) ?z |- _ => inv H
      |H:Ensembles.In _ (Singleton _ ?x) ?y |- _ => inv H
  end. 

Theorem validEnvDomainUnique : forall Gamma C eta' eta i U, 
                                 setVertices Gamma C i eta' eta ->
                                 (forall x, Ensembles.In _ U x -> x < 3 * i) -> 
                                 genericUnique U (fun a => match a with (x,y) => x end) eta'. 
Proof.
  intros. genDeps {{ U }}. induction H; intros. 
  {constructor. constructor. constructor. eapply IHsetVertices. intros. inSet. inSet.
   inSet. apply H1 in H3. omega. inSet. omega. inSet. omega. inSet. omega. intros c. inSet. 
   inSet. apply H1 in H3. omega. inSet. omega. inSet. omega. intros c. inSet. apply H1 in H2. 
   omega. inSet. omega. intros c. apply H1 in c. omega. }
  {constructor. constructor. constructor. eapply IHsetVertices. intros. inSet. inSet.
   inSet. apply H1 in H3. omega. inSet. omega. inSet. omega. inSet. omega. intros c. inSet. 
   inSet. apply H1 in H3. omega. inSet. omega. inSet. omega. intros c. inSet. apply H1 in H2. 
   omega. inSet. omega. intros c. apply H1 in c. omega. }
  {constructor. }
Qed. 

Theorem KColorNPC : forall Gamma Delta F C eta G eta' U,
                      reduce Gamma Delta F C G -> 
                      valid Gamma C F eta' eta -> genericUnique U (fun x => x) Delta -> 
                      (SAT' eta F <-> coloring eta' G C).
Proof. 
  intros. inv H. split; intros. 
  {constructor. 
   {
admit. }
   {constructor. 
    {inv H0. eapply colorWeakening. eapply cliqueColorable; eauto. }
    {inv H0. apply colorWeakening. eapply varsToCliqueColorable; eauto. }
   }
  }
  {admit. }
Qed. 

Theorem buildCtxtUnique : forall i n Gamma Delta U, 
                            buildCtxt n i Gamma Delta -> 
                            (forall x, Ensembles.In vvar U x -> x < i) -> 
                            genericUnique U (fun x=> x) Delta. 
Proof.
  intros. generalize dependent U. induction H; intros. 
  {constructor. eapply IHbuildCtxt. intros. inSet. apply H0 in H2. 
   auto. inSet. omega. intros c. apply H0 in c. omega. }
  {constructor. }
Qed. 

Theorem KColorNPCTopLevel : forall Gamma Delta F n G eta eta', 
                              buildCtxt n 0 Gamma Delta ->
                              reduce Gamma Delta F (n+1) G -> valid Gamma (n+1) F eta' eta ->
                              (SAT' eta F <-> coloring eta' G (n+1)). 
Proof.
  intros. apply buildCtxtUnique with (U:=Empty_set _) in H. Focus 2. intros. 
  inv H2. eapply KColorNPC in H0; eauto. 
Qed. 


