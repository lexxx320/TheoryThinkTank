Require Import ThreeSatReduction.  




Theorem convStackOutOfScope : forall eta'' eta' i Gamma Delta K G j c C eta, 
                                convStack i Gamma Delta K G ->j < i -> 
                                setVertices Gamma C 0 eta' eta -> setCs eta' i K eta'' eta ->
                                coloring (eta'++(j,c)::eta'') G C ->
                                coloring (eta'++eta'') G C. 
Proof.
  intros. genDeps {{ eta; eta'; eta''; j; C; c }}. induction H; intros. 
  {constructor. }
  {constructor. 


Fixpoint graphFVs G :=
  match G with
    |emptyGraph => []
    |newEdge u v G => u::v::graphFVs G
    |gunion G1 G2 => graphFVs G1 ++ graphFVs G2
  end.

Ltac solveIn :=
  match goal with
      | |- In ?x (?a ++ ?b) => rewrite in_app_iff; 
                            solve[left; solveIn|right; solveIn]
      | |- In ?a ?b \/ In ?c ?d => simpl in *; solve[left; solveIn | right; solveIn]
      | |- In ?a (?b::?c) => simpl; solve[left; auto|right; solveIn]
      | |- _ => eauto
  end. 

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
Proof.
  induction L1; intros. 
  {simpl. auto. }
  {simpl in *. intros c. apply H. inv c; auto. rewrite in_app_iff in H1. 
   inv H1. auto. contradiction. }
Qed. 

Theorem notInFV : forall Gamma C eta1 eta Delta G j K i eta2, 
                    setVertices Gamma C 0 eta1 eta -> setCs eta1 i K eta2 eta ->
                    j < i -> convStack i Gamma Delta K G -> ~ In j (graphFVs G). 
Proof.
  intros. genDeps {{ j; eta; eta1; eta2 }}. induction H2; intros.
  {intros c. inv c. }
  {simpl. apply notInDistribute. inv H1; eapply IHconvStack; eauto;
   rewrite plus_comm; eauto. destruct F. destruct p. inv H. simpl. 
   destruct e1. destruct e2. destruct e3. simpl. 


Theorem notInFVFormula : forall Gamma C eta1 eta Delta G j F i eta2, 
                           setVertices Gamma C 0 eta1 eta -> setCs eta1 i K eta2 eta ->
                           j < i -> convFormula i Gamma Delta F G -> ~ In j (graphFVs G). 
Proof.

Theorem colorImpliesSATFormula : forall Gamma C eta eta' i U eta'' Delta F G,
                            setVertices Gamma C 0 eta' eta -> setCs eta' i F eta'' eta ->
                            coloring (eta'++eta'') G C -> i >= 3 * length Gamma ->
                            genericUnique U (fun x => x) Delta -> 
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
     rewrite plus_comm. eauto. Focus 3. eauto. Focus 2. eauto. admit. omega. eauto. }
   }
   {inv H12. 
    {constructor. right. left. constructor. auto. eapply IHconvStack. Focus 3.
     rewrite plus_comm. eauto. Focus 3. eauto. Focus 2. eauto. admit. }
    {constructor. right. left. constructor. auto. eapply IHconvStack. Focus 3.
     rewrite plus_comm. eauto. Focus 3. eauto. Focus 2. eauto. admit. }
   }
   {inv H12. 
    {constructor. right. right. constructor. auto. eapply IHconvStack. Focus 3.
     rewrite plus_comm. eauto. Focus 3. eauto. Focus 2. eauto. admit. }
    {constructor. right. right. constructor. auto. eapply IHconvStack. Focus 3.
     rewrite plus_comm. eauto. Focus 3. eauto. Focus 2. eauto. admit. }
   }
  }
Qed. 


