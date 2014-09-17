Require Import ThreeSatReduction.   




Theorem convertBaseColorable : forall i Gamma Delta G F eta S5 eta'' eta' C, 
                                 setVertices Gamma C 0 eta' eta -> 
                                 setCs eta' (3 * length Gamma) F eta'' eta -> 
                                 genericUnique S5 (fun x => x) Delta -> 
                                 convert_base Gamma Delta i G -> coloring eta' G C.
Admitted. 

Theorem colorWeakeningApp : forall eta1 eta2 eta3 G C,
                           coloring (eta1++eta3) G C ->
                           coloring (eta1++eta2++eta3) G C. 
Proof.
  intros. genDeps {{ eta2 }}. remember(eta1++eta3). induction H; intros. 
  {constructor. }
  {subst. econstructor. apply in_app_iff in H. inv H. auto. apply in_app_iff; simpl.
   eauto. repeat rewrite in_app_iff. auto. apply in_app_iff in H0. inv H0; 
   repeat rewrite in_app_iff; eauto. auto. auto. auto. eapply IHcoloring; eauto. }
  {constructor; eauto. }
Qed. 

Theorem consApp : forall (A:Type) (hd:A) tl, hd::tl = [hd]++tl. auto. Qed. 
Theorem plus0 : forall n, n = n + 0. auto. Qed. 

Ltac negate H :=
  match type of H with
      |?x => assert(~ x)
  end. 

Theorem InEtaInEta' : forall u c b Gamma C i eta eta', In (u, b) eta -> In (3*u, c) eta' -> 
                                            setVertices Gamma C i eta' eta -> 
                                            (c = u /\ In (u, true) eta) \/ (c = C /\ In (u, false) eta). 
Proof.
  intros. genDeps {{ u; c; b }}. induction H1; intros. 
  {destruct (eq_nat_dec u u0). 
   {subst. inCons. invertTupEq. left. split; simpl; auto. inCons. invertTupEq. omega. 
    inCons. invertTupEq. omega. negate H3. assert(3*u0=3*u0+0) by auto. rewrite H2. 
    eapply notInEta; eauto. contradiction. }
   {inCons. invertTupEq. omega. inCons. invertTupEq. omega. inCons. invertTupEq. 
    omega. inCons. invertTupEq. omega. eapply IHsetVertices in H3; eauto. inv H3. invertHyp. 
    left. split; simpl; auto. invertHyp. right. split; simpl; auto. }
  }
  {destruct (eq_nat_dec u u0). 
   {subst. inCons. invertTupEq. right. split; simpl; auto. inCons. invertTupEq. omega. 
    inCons. invertTupEq. omega. negate H3. assert(3*u0=3*u0+0) by auto. rewrite H2. 
    eapply notInEta; eauto. contradiction. }
   {inCons. invertTupEq. omega. inCons. invertTupEq. omega. inCons. invertTupEq. 
    omega. inCons. invertTupEq. omega. eapply IHsetVertices in H3; eauto. inv H3. invertHyp. 
    left. split; simpl; auto. invertHyp. right. split; simpl; auto. }
  }
  {inv H. }
Qed. 


Theorem lookupEta'Det : forall Gamma C i eta eta' epsilon u c1 c2, setVertices Gamma C i eta' eta ->
                                         In (3*u+epsilon, c1) eta' -> In (3*u+epsilon, c2) eta' -> c1=c2 . 
Proof.
  intros. induction H. 
  {destruct (eq_nat_dec u u0). 
   {subst. inCons. invertTupEq. inCons. invertTupEq. auto. inCons. 
    invertTupEq. omega. inCons. invertTupEq. auto. negate H1. eapply notInEta; eauto. 
    destruct epsilon. auto. omega. contradiction. inCons. invertTupEq. inCons. invertTupEq. 
    omega. inCons. invertTupEq. auto. inCons. invertTupEq. omega. negate H1.
    eapply notInEta; eauto. destruct epsilon. auto. omega. contradiction. inCons. invertTupEq. 
    inCons. invertTupEq. auto. inCons. invertTupEq. omega. inCons. invertTupEq. auto.
    negate H1. eapply notInEta; eauto. destruct epsilon. auto. omega. contradiction. inCons. 
    invertTupEq. negate H3. eapply notInEta; eauto. destruct epsilon. auto. omega. contradiction. 
    inCons. invertTupEq. negate H3. eapply notInEta; eauto. destruct epsilon. auto. omega. 
    contradiction. inCons. invertTupEq. negate H3. eapply notInEta; eauto. destruct epsilon. 
    auto. omega. contradiction. eapply IHsetVertices; eauto. }
   {subst. inCons. invertTupEq. destruct epsilon. omega. destruct epsilon. omega. 

invertTupEq. inCons. invertTupEq. auto. inCons. 
    invertTupEq. omega. inCons. invertTupEq. auto. negate H1. eapply notInEta; eauto. 
    omega. destruct epsilon. auto. omega. contradiction. inCons. invertTupEq. inCons. invertTupEq. 
    omega. inCons. invertTupEq. auto. inCons. invertTupEq. omega. negate H1.
    eapply notInEta; eauto. destruct epsilon. auto. omega. contradiction. inCons. invertTupEq. 
    inCons. invertTupEq. auto. inCons. invertTupEq. omega. inCons. invertTupEq. auto.
    negate H1. eapply notInEta; eauto. destruct epsilon. auto. omega. contradiction. inCons. 
    invertTupEq. negate H3. eapply notInEta; eauto. destruct epsilon. auto. omega. contradiction. 
    inCons. invertTupEq. negate H3. eapply notInEta; eauto. destruct epsilon. auto. omega. 
    contradiction. inCons. invertTupEq. negate H3. eapply notInEta; eauto. destruct epsilon. 
    auto. omega. contradiction. eapply IHsetVertices; eauto. }


Theorem helper : forall Gamma C p1 eta eta' i c G u eta'' v v0 u', 
              u = getVar p1 -> setVertices Gamma C 0 eta' eta -> In (u,3*u,3*u+1,3*u+2) Gamma -> winner eta p1 u' ->
              mkEdge i p1 (3*u) (3*u+1) (v,v0) -> In (3 * u', c) eta' -> 
              coloring(eta' ++ (i,c)::eta'') G C ->
              coloring(eta' ++ (i,c)::eta'') (newEdge v v0 G) C.
Proof.
  intros. inversion H3; subst. 
  {inv H2. 
   {copy H1. eapply V_V'MapToUOrC in H1; eauto. inv H1. 
    {invertHyp. eapply InEtaInEta' in H6; eauto. simpl in *. inv H6. 
     {admit. }
     {invertHyp. econstructor. apply in_app_iff. right. simpl. eauto. apply in_app_iff. 
      left. eauto. auto. omega. omega. omega.  auto. }
    }
    {invertHyp. econstructor. apply in_app_iff. right. simpl. eauto. apply in_app_iff. 
     left. eauto. 

Theorem convFormulaColorable : forall i Gamma Delta G eta K U eta'' F eta' C, 
                                 setVertices Gamma C 0 eta' eta -> SAT' eta (F::K) ->
                                 setCs eta' i (F::K) eta'' eta -> 
                                 genericUnique U (fun x => x) Delta -> 
                                 convFormula i Gamma Delta F G -> coloring (eta'++eta'') G C.
Proof. 
  intros. inv H3. simpl. destruct e1. destruct e2. destruct e3.
  {inv H1.  
   {inversion H8; subst. simpl in *. 
    {inv H18.  
     {copy H4. eapply V_V'MapToUOrC in H4; eauto. inv H4. 
      {invertHyp. inv H0. econstructor. apply in_app_iff. simpl. right. eauto. 
       apply in_app_iff. left. eauto. 



 copy H3. eapply InEtaInEta' in H3; eauto. inv H3. 
       {invertHyp. econstructor. apply in_app_iff. right. simpl. eauto. apply in_app_iff. 
        left. eauto. 

Focus 2. 
       invertHyp. econstructor. apply in_app_iff. right. simpl. eauto. apply in_app_iff.
       left. eauto. auto. omega. omega. omega. 



Theorem A : forall Gamma u C eta eta', 
              setVertices Gamma C 0 eta' eta -> In (u,3*u,3*u+1,3*u+2) Gamma ->
              coloring

Theorem convStackColorable : forall i Gamma Delta G eta F j S5 eta'' eta' C, 
                               setVertices Gamma C 0 eta' eta -> 
                               setCs eta' j F eta'' eta ->
                               genericUnique S5 (fun x => x) Delta -> 
                               convStack i Gamma Delta F G -> coloring (eta' ++ eta'') G C.
Proof.
  intros. genDeps {{ S5; eta; eta'; C; eta''; j }}. induction H2; intros. 
  {constructor. }
  {constructor. 
   {inv H1. 
    {rewrite consApp. apply colorWeakeningApp. eapply IHconvStack; eauto. }
    {rewrite consApp. apply colorWeakeningApp. eapply IHconvStack; eauto. }
    {rewrite consApp. apply colorWeakeningApp. eapply IHconvStack; eauto. }
   }
   {eapply convFormulaColorable; eauto. }
  }
Qed. 






  



























ad;lfkhjasdf

