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


 

     eapply convStackOutOfScope. eauto. Focus 2. eauto. Focus 2. rewrite plus_comm. 
     eauto. Focus 2. inv H1. eauto. omega. }
    {constructor. left. constructor. auto. eapply IHconvStack. Focus 3.
     rewrite plus_comm. eauto. Focus 3. eauto. Focus 2. eauto. admit. }
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


