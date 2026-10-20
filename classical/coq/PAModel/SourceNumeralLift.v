(** Lift finite source syntax and derivations into every PA model. The
    induction is on a fixed external derivation; this makes no assertion
    that an arbitrary internal proof is externally finite. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT Pairing CodeExpressions
  StandardModel SetFormulaCodes SetCodeDescent ZFCFiniteSourceCodes FixedSourceBounds SourceBounded SourceBoundedCalibration
  SchemaRenamingDescriptors SourceFiniteContexts NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  SubstitutionSource RenamingSubstitution NumericalInstantiation SourceSequents
  SourceQuantifierRules NumericalSourceFull.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.Facts Syntax.BinSig
  Sets.Signatures Deduction.FullND.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.

Lemma source_numeral_pair M a b :
  pair_graph M (code_numeral M a) (code_numeral M b)
    (code_numeral M (KCode230.P a b)).
Proof.
  pose proof (proj2 (pair_graph_natModel a b (KCode230.P a b)) eq_refl) as HP.
  change (2 * KCode230.P a b = (a+b)*S(a+b)+2*b) in HP.
  unfold pair_graph,twoM. rewrite descriptor_numeral_add.
  change (mulM M (code_numeral M 2) (code_numeral M (KCode230.P a b)) =
    addM M (mulM M (code_numeral M (a+b)) (code_numeral M (S(a+b))))
      (mulM M (code_numeral M 2) (code_numeral M b))).
  rewrite !descriptor_numeral_mul,descriptor_numeral_add,HP. reflexivity.
Qed.

Theorem code_relation_numeral M env expression :
  code_relation M (fun i => code_numeral M (env i)) expression
    (code_numeral M (code_value env expression)).
Proof.
  induction expression as [n|i|a IHa b IHb|a IHa b IHb|a IHa b IHb];
    cbn [code_relation code_value].
  - reflexivity.
  - reflexivity.
  - exists (code_numeral M (code_value env a)),
      (code_numeral M (code_value env b)).
    split;[exact IHa|]. split;[exact IHb|].
    symmetry. apply descriptor_numeral_add.
  - exists (code_numeral M (code_value env a)),
      (code_numeral M (code_value env b)).
    split;[exact IHa|]. split;[exact IHb|].
    symmetry. apply descriptor_numeral_mul.
  - exists (code_numeral M (code_value env a)),
      (code_numeral M (code_value env b)).
    split;[exact IHa|]. split;[exact IHb|].
    apply source_numeral_pair.
Qed.

Lemma sf_make_numeral M h a b :
  sf_relation M h (code_numeral M a) (code_numeral M b)
    (code_numeral M (sf_make h a b)).
Proof.
  unfold sf_relation,sf_make.
  apply (proj2 (code_relation_ext M (E_sf h (CEvar 0) (CEvar 1))
    (sf_env (code_numeral M a) (code_numeral M b))
    (fun i => code_numeral M (sf_env a b i)) _ ltac:(intros [|i];reflexivity))).
  apply code_relation_numeral.
Qed.

Lemma source_formula_numeral_graph {ff} M
    (phi : source_form_with ff) :
  code_relation M (fun _=>zeroM M) (sf_expression phi)
    (code_numeral M (sf_encode phi)).
Proof.
  rewrite <- (sf_expression_value (fun _=>0) phi).
  exact (code_relation_numeral M (fun _=>0) (sf_expression phi)).
Qed.

Theorem source_formula_numeral_bounded {ff} M (phi : source_form_with ff) n :
  source_bounded M (code_numeral M (sf_encode phi)) (code_numeral M n) <-> bounded n phi.
Proof.
  exact (fixed_source_bounded_iff phi M (fun _=>zeroM M)
    (code_numeral M (sf_encode phi)) n (source_formula_numeral_graph M phi)).
Qed.

Lemma source_numeral_initial_segment M n x :
  coding_lt M x (code_numeral M n) -> exists i, i<n /\ x=code_numeral M i.
Proof.
  induction n as [|n IH]; intro Hx.
  - exfalso. exact (coding_not_lt_zero M x Hx).
  - change (coding_lt M x (succM M (code_numeral M n))) in Hx.
    apply (proj1 (coding_lt_succ_cases M x (code_numeral M n))) in Hx.
    destruct Hx as [Hx|Hx].
    + destruct (IH Hx) as [i [Hi Ei]]. exists i. split;[lia|exact Ei].
    + exists n. split;[lia|exact Hx].
Qed.

Definition source_model_context_represents {ff} (M : Model) (b c n : carrier M)
    (A : list (source_form_with ff)) : Prop :=
  n=code_numeral M (List.length A) /\
  forall (i:nat) (phi:source_form_with ff),@eq _ (List.nth_error A i) (Some phi) ->
    beta M b c (code_numeral M i) (code_numeral M (sf_encode phi)).

Lemma source_numeral_beta M b c i r :
  beta natModel b c i r ->
  beta M (code_numeral M b) (code_numeral M c) (code_numeral M i) (code_numeral M r).
Proof.
  intros [Hr [q Hb]]. apply (descriptor_beta_certificate M b c i r q).
  - apply sb_coding_lt_nat in Hr. exact Hr.
  - exact Hb.
Qed.

Theorem source_model_context_lift {ff} M b c n (A:list(source_form_with ff)) :
  source_context_represents b c n A ->
  source_model_context_represents M (code_numeral M b) (code_numeral M c) (code_numeral M n) A.
Proof.
  intros [En HA]. split;[now rewrite En|].
  intros i phi Hi. apply source_numeral_beta. exact (HA i phi Hi).
Qed.

Theorem source_model_context_empty {ff} M b c :
  source_model_context_represents M b c (zeroM M) (@nil (source_form_with ff)).
Proof. split;[reflexivity|]. intros [|i] phi H;discriminate. Qed.

Theorem source_model_context_cons {ff} M b c n (A:list(source_form_with ff)) phi d e m :
  source_model_context_represents M b c n A ->
  environment_cons M b c n (code_numeral M (sf_encode phi)) d e m ->
  source_model_context_represents M d e m (phi::A).
Proof.
  intros [En HA] HC. split.
  - rewrite (proj1 HC),En. reflexivity.
  - intros [|i] psi Hi.
    + cbn in Hi. inversion Hi;subst psi.
      assert (Hm : coding_lt M (zeroM M) m).
      { rewrite (proj1 HC). apply coding_zero_lt_succ. }
      apply (proj1 (environment_lookup_inside M d e m (zeroM M) _ Hm)).
      exact (proj1 (proj2 HC)).
    + cbn in Hi.
      assert (Hlt : coding_lt M (code_numeral M i) n).
      { rewrite En. apply (proj2 (fixed_source_numeral_lt_iff M i (List.length A))).
        apply List.nth_error_Some. rewrite Hi. discriminate. }
      assert (Hm : coding_lt M (code_numeral M (S i)) m).
      { rewrite (proj1 HC). apply (proj2 (coding_lt_succ_cancel M _ _)). exact Hlt. }
      apply (proj1 (environment_lookup_inside M d e m _ _ Hm)).
      apply (proj2 (proj2 HC)).
      apply (proj2 (environment_lookup_inside M b c n _ _ Hlt)). exact (HA i psi Hi).
Qed.

Theorem source_model_context_total {ff} M (A:list(source_form_with ff)) :
  exists b c n,source_model_context_represents M b c n A.
Proof.
  induction A as [|phi A [b [c [n HA]]]].
  - exists (zeroM M),(zeroM M),(zeroM M). apply source_model_context_empty.
  - destruct (environment_cons_total M b c n (code_numeral M (sf_encode phi)))
      as [d [e [m HC]]]. exists d,e,m.
    exact (source_model_context_cons M b c n A phi d e m HA HC).
Qed.

Theorem source_model_context_member_iff {ff} M b c n (A:list(source_form_with ff)) f :
  source_model_context_represents M b c n A ->
  (context_member M b c n f <->
    exists phi,List.In phi A /\ f=code_numeral M (sf_encode phi)).
Proof.
  intros [En HA]. split.
  - intros [x [Hx HF]]. rewrite En in Hx.
    destruct (source_numeral_initial_segment M (List.length A) x Hx) as [i [Hi ->]].
    assert (Hex : exists phi:source_form_with ff,@eq _ (List.nth_error A i) (Some phi)).
    { destruct (List.nth_error A i) as [phi|] eqn:E;[now exists phi|].
      apply List.nth_error_None in E. lia. }
    destruct Hex as [phi Hphi]. exists phi. split.
    + exact (List.nth_error_In A i Hphi).
    + exact (beta_unique M b c (code_numeral M i) f (code_numeral M (sf_encode phi))
        HF (HA i phi Hphi)).
  - intros [phi [Hin ->]]. apply List.In_nth_error in Hin as [i Hi].
    exists (code_numeral M i). split.
    + rewrite En. apply (proj2 (fixed_source_numeral_lt_iff M i (List.length A))).
      apply List.nth_error_Some. rewrite Hi. discriminate.
    + exact (HA i phi Hi).
Qed.

Theorem source_model_context_bound {ff} M b c n (A:list(source_form_with ff)) k :
  source_model_context_represents M b c n A ->
  (forall phi,List.In phi A -> bounded k phi) ->
  context_bounded M b c n (code_numeral M k).
Proof.
  intros HR HB f Hf.
  apply (proj1 (source_model_context_member_iff M b c n A f HR)) in Hf.
  destruct Hf as [phi [Hin ->]].
  apply (proj2 (source_formula_numeral_bounded M phi k)). exact (HB phi Hin).
Qed.

Theorem source_model_context_sequent_wf {ff} M b c n (A:list(source_form_with ff)) phi :
  source_model_context_represents M b c n A ->
  source_sequent_wf M b c n (code_numeral M (sf_encode phi)).
Proof.
  intro HR. destruct (find_bounded_L (phi::A)) as [k Hk].
  exists (code_numeral M k). split.
  - apply (proj2 (source_formula_numeral_bounded M phi k)). apply Hk. now left.
  - apply (source_model_context_bound M b c n A k HR).
    intros psi Hpsi. apply Hk. now right.
Qed.

Theorem source_model_context_branches_wf {ff} M b c n (A:list(source_form_with ff)) phi psi theta :
  source_model_context_represents M b c n A ->
  source_branches_wf M b c n (code_numeral M (sf_encode phi))
    (code_numeral M (sf_encode psi)) (code_numeral M (sf_encode theta)).
Proof.
  intro HR. destruct (find_bounded_L (phi::psi::theta::A)) as [k Hk].
  exists (code_numeral M k). split.
  - apply (proj2 (source_formula_numeral_bounded M phi k)). apply Hk. now left.
  - split.
    + apply (proj2 (source_formula_numeral_bounded M psi k)). apply Hk. right;now left.
    + split.
      * apply (proj2 (source_formula_numeral_bounded M theta k)). apply Hk. right;right;now left.
      * apply (source_model_context_bound M b c n A k HR).
        intros eta HE. apply Hk. right;right;now right.
Qed.

Theorem source_formula_numeral_instantiation {ff} M (phi:source_form_with ff) (t:sf_term) :
  numerical_instantiation M (code_numeral M (sf_encode phi)) (code_numeral M (sf_index t))
    (code_numeral M (sf_encode (subst_form (t .: var) phi))).
Proof.
  destruct (substitution_singleton_total M (code_numeral M (sf_index t))) as [b [c [HH HT]]].
  exists b,c. split;[exact HH|].
  exact (fixed_source_singleton_substitution M (fun _=>zeroM M) phi t b c _ _ HH
    (source_formula_numeral_graph M phi)
    (source_formula_numeral_graph M (subst_form (t .: var) phi))).
Qed.

Theorem source_formula_numeral_shift {ff} M (phi:source_form_with ff) :
  source_formula_shift M (code_numeral M (sf_encode phi))
    (code_numeral M (sf_encode (subst_form ↑ phi))).
Proof.
  apply (proj2 (numerical_renaming_empty_substitution M _ (zeroM M) (zeroM M)
    (succM M (zeroM M)) _)).
  apply (fixed_source_substitution M (fun _=>zeroM M) phi ↑
    (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M))).
  - intro i. apply substitution_lookup_outside.
    + apply coding_not_lt_zero.
    + exists (code_numeral M i). split;[symmetry;apply coding_add_zero|].
      change (succM M (code_numeral M i)=addM M (succM M (zeroM M)) (code_numeral M i)).
      now rewrite Arithmetic.add_succ,coding_add_zero.
  - apply source_formula_numeral_graph.
  - apply source_formula_numeral_graph.
Qed.

Theorem source_model_context_shift {ff} M b c n (A:list(source_form_with ff)) d e :
  source_model_context_represents M b c n A -> context_shift M b c n d e ->
  source_model_context_represents M d e n (List.map (subst_form ↑) A).
Proof.
  intros [En HA] HS. split;[now rewrite List.length_map|].
  intros i phi Hphi. rewrite List.nth_error_map in Hphi.
  assert (Hmap : forall (o : option(source_form_with ff)) (phi:source_form_with ff),
    @eq _ (option_map (subst_form ↑) o) (Some phi) ->
    exists psi:source_form_with ff,@eq _ o (Some psi) /\ subst_form ↑ psi=phi).
  { intros [psi|] eta HE;cbn in HE;inversion HE;subst;eauto. }
  destruct (Hmap (List.nth_error A i) phi Hphi) as [psi [Hi HE]]. subst phi.
  assert (Hlt : coding_lt M (code_numeral M i) n).
  { rewrite En. apply (proj2 (fixed_source_numeral_lt_iff M i (List.length A))).
    apply List.nth_error_Some. rewrite Hi. discriminate. }
  destruct (beta_total M d e (code_numeral M i)) as [g Hg].
  pose proof (HS (code_numeral M i) (code_numeral M (sf_encode psi)) g
    Hlt (HA i psi Hi) Hg) as HR.
  assert (E : g=code_numeral M (sf_encode (subst_form ↑ psi))).
  { exact (numerical_renaming_functional M _ (zeroM M) (zeroM M) (zeroM M)
      (succM M (zeroM M)) _ _ HR (source_formula_numeral_shift M psi)). }
  now rewrite <- E.
Qed.

Theorem source_full_forward_model {ff p} M (A:list(source_form_with ff)) (phi:source_form_with ff) :
  @FullND.prv sig_empty ZFSignature.ZF_pred_sig ff p A phi ->
  forall b c n, source_model_context_represents M b c n A ->
    source_full_prv M b c n (code_numeral M (sf_encode phi)).
Proof.
  intro H. revert M. induction H as
    [ff p A a d H IH
    |ff p A a d H1 IH1 H2 IH2
    |ff p A a H IH
    |ff p A t a H IH
    |ff p A t a H IH
    |ff p A a d H1 IH1 H2 IH2
    |p A a H IH
    |ff p A a Hin
    |ff p A a d H1 IH1 H2 IH2
    |ff p A a d H IH
    |ff p A a d H IH
    |ff p A a d H IH
    |ff p A a d H IH
    |ff p A a d f H0 IH0 H1 IH1 H2 IH2
    |ff A a d]; intros M b c n HR.
  all: match goal with |- source_full_prv ?model ?eb ?ec ?en ?v =>
    assert (HW : source_sequent_wf model eb ec en v)
      by (eapply source_model_context_sequent_wf; exact HR) end.
  - destruct (environment_cons_total M b c n (code_numeral M (sf_encode a))) as [u [v [l HC]]].
    eapply full_source_II; [exact HW| |exact HC|apply sf_make_numeral].
    apply IH. exact (source_model_context_cons M b c n A a u v l HR HC).
  - eapply full_source_IE; [exact HW|apply IH1;exact HR|apply IH2;exact HR|apply sf_make_numeral].
  - destruct (context_shift_total M b c n) as [u [v HS]].
    eapply full_source_AllI; [exact HW| |exact HS|exact (sf_make_numeral M SFAll (sf_encode a) 0)].
    apply IH. exact (source_model_context_shift M b c n A u v HR HS).
  - eapply full_source_AllE; [exact HW|apply IH;exact HR|exact (sf_make_numeral M SFAll (sf_encode a) 0)|apply source_formula_numeral_instantiation].
  - eapply full_source_ExI; [exact HW|apply IH;exact HR|exact (sf_make_numeral M SFEx (sf_encode a) 0)|apply source_formula_numeral_instantiation].
  - destruct (context_shift_total M b c n) as [u [v HS]].
    destruct (environment_cons_total M u v n (code_numeral M (sf_encode a))) as [x [y [l HC]]].
    eapply full_source_ExE; [exact HW|apply IH1;exact HR| |exact (sf_make_numeral M SFEx (sf_encode a) 0)|exact HS|exact HC|apply source_formula_numeral_shift].
    apply IH2. eapply source_model_context_cons; [|exact HC].
    exact (source_model_context_shift M b c n A u v HR HS).
  - apply (full_source_Exp M b c n (code_numeral M (sf_encode a)) HW). exact (IH M b c n HR).
  - apply (full_source_Ctx M b c n (code_numeral M (sf_encode a)) HW).
    apply (proj2 (source_model_context_member_iff M b c n A (code_numeral M (sf_encode a)) HR)). exists a. auto.
  - eapply full_source_CI; [exact HW|apply IH1;exact HR|apply IH2;exact HR|apply sf_make_numeral].
  - eapply full_source_CE1; [exact HW|apply IH;exact HR|apply sf_make_numeral].
  - eapply full_source_CE2; [exact HW|apply IH;exact HR|apply sf_make_numeral].
  - eapply full_source_DI1; [exact HW|apply IH;exact HR|apply sf_make_numeral].
  - eapply full_source_DI2; [exact HW|apply IH;exact HR|apply sf_make_numeral].
  - destruct (environment_cons_total M b c n (code_numeral M (sf_encode a))) as [u [v [l HC]]].
    destruct (environment_cons_total M b c n (code_numeral M (sf_encode d))) as [x [y [k HD]]].
    eapply full_source_DE_three; [exact HW| |apply IH0;exact HR| | |exact HC|exact HD|apply sf_make_numeral].
    + exact (source_model_context_branches_wf M b c n A a d f HR).
    + apply IH1. exact (source_model_context_cons M b c n A a u v l HR HC).
    + apply IH2. exact (source_model_context_cons M b c n A d x y k HR HD).
  - eapply full_source_Pc; [exact HW|apply sf_make_numeral|apply sf_make_numeral|apply sf_make_numeral].
Qed.

Corollary source_full_forward_model_empty {ff p} M (phi:source_form_with ff) :
  @FullND.prv sig_empty ZFSignature.ZF_pred_sig ff p (@nil (source_form_with ff)) phi ->
  source_full_prv M (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M (sf_encode phi)).
Proof.
  intro H. apply (source_full_forward_model M (@nil (source_form_with ff)) phi H).
  apply source_model_context_empty.
Qed.

Corollary source_full_forward_model_lift {ff p} M (A:list(source_form_with ff))
    (phi:source_form_with ff) b c n :
  @FullND.prv sig_empty ZFSignature.ZF_pred_sig ff p A phi ->
  source_context_represents b c n A ->
  source_full_prv M (code_numeral M b) (code_numeral M c) (code_numeral M n)
    (code_numeral M (sf_encode phi)).
Proof.
  intros HP HC. apply (source_full_forward_model M A phi HP).
  exact (source_model_context_lift M b c n A HC).
Qed.

Print Assumptions code_relation_numeral.
Print Assumptions source_formula_numeral_instantiation.
Print Assumptions source_model_context_shift.
Print Assumptions source_full_forward_model.
Print Assumptions source_full_forward_model_empty.
Print Assumptions source_full_forward_model_lift.
