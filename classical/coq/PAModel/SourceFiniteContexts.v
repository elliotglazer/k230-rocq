(** Finite-library contexts represented by exact-length numerical beta tables.
    This is standard-model calibration, not a restriction on the numerical
    calculus or a proof about arbitrary nonstandard derivations. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs StandardModel SetFormulaCodes SourceBounded SourceBoundedCalibration
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming
  NumericalRenamingMaps RenamingPayloads SchemaRenamingCalibration SetSchemaConstructors
  NumericalInstantiation NumericalSubstitutionMaps NumericalSubstitution SubstitutionSource
  SourceSequents SourceQuantifierRules.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.Facts Syntax.BinSig Sets.Signatures.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.

Definition source_form_with ff := @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff.

Definition source_context_represents {ff} b c n (A : list (source_form_with ff)) :=
  n = List.length A /\ forall i phi, List.nth_error A i = Some phi -> beta natModel b c i (sf_encode phi).

Theorem source_context_empty {ff} b c :
  source_context_represents b c 0 (@nil (source_form_with ff)).
Proof. split; [reflexivity|]. intros [|i] phi H; discriminate. Qed.

Theorem source_context_cons {ff} b c n (A:list(source_form_with ff)) phi d e m :
  source_context_represents b c n A -> environment_cons natModel b c n (sf_encode phi) d e m ->
  source_context_represents d e m (phi::A).
Proof.
  intros [En HA] HC. split; [change (m = S(List.length A)); rewrite (proj1 HC),En; reflexivity|].
  intros [|i] psi Hi.
  - cbn in Hi. inversion Hi; subst psi.
    assert (H0 : coding_lt natModel 0 m) by (rewrite (proj1 HC);apply coding_zero_lt_succ).
    apply (proj1 (environment_lookup_inside natModel d e m 0 (sf_encode phi) H0)).
    exact (proj1 (proj2 HC)).
  - cbn in Hi. assert (Hlt : coding_lt natModel i n).
    { apply sb_coding_lt_nat. rewrite En. apply List.nth_error_Some. rewrite Hi. discriminate. }
    assert (HS : coding_lt natModel (S i) m).
    { rewrite (proj1 HC). exact (proj2 (coding_lt_succ_cancel natModel i n) Hlt). }
    apply (proj1 (environment_lookup_inside natModel d e m (S i) (sf_encode psi) HS)).
    apply (proj2 (proj2 HC)). apply (proj2 (environment_lookup_inside natModel b c n i (sf_encode psi) Hlt)).
    exact (HA i psi Hi).
Qed.

Theorem source_context_total {ff} (A:list(source_form_with ff)) :
  exists b c n, source_context_represents b c n A.
Proof.
  induction A as [|phi A [b [c [n H]]]].
  - exists 0,0,0. apply source_context_empty.
  - destruct (environment_cons_total natModel b c n (sf_encode phi)) as [d [e [m HC]]].
    exists d,e,m. exact (source_context_cons b c n A phi d e m H HC).
Qed.

Theorem source_context_member_iff {ff} b c n (A:list(source_form_with ff)) f :
  source_context_represents b c n A ->
  (context_member natModel b c n f <-> exists phi, List.In phi A /\ f = sf_encode phi).
Proof.
  intros [En HA]. split.
  - intros [i [Hi Hf]]. apply sb_coding_lt_nat in Hi. rewrite En in Hi.
    assert (Hex : exists phi, List.nth_error A i = Some phi).
    { destruct (List.nth_error A i) as [phi|] eqn:E; [now exists phi|].
      apply List.nth_error_None in E. lia. }
    destruct Hex as [phi Hphi]. exists phi. split.
    + exact (List.nth_error_In A i Hphi).
    + exact (beta_unique natModel b c i f (sf_encode phi) Hf (HA i phi Hphi)).
  - intros [phi [Hin ->]]. apply List.In_nth_error in Hin as [i Hi].
    exists i. split.
    + apply sb_coding_lt_nat. rewrite En. apply List.nth_error_Some. rewrite Hi. discriminate.
    + exact (HA i phi Hi).
Qed.

Theorem source_context_bound {ff} b c n (A:list(source_form_with ff)) k :
  source_context_represents b c n A ->
  (forall phi, List.In phi A -> bounded k phi) -> context_bounded natModel b c n k.
Proof.
  intros HR HB f Hf. apply (proj1 (source_context_member_iff b c n A f HR)) in Hf.
  destruct Hf as [phi [Hin ->]]. apply (proj2 (source_bounded_sf_encode phi k)). exact (HB phi Hin).
Qed.

Theorem source_context_sequent_wf {ff} b c n (A:list(source_form_with ff)) phi :
  source_context_represents b c n A -> source_sequent_wf natModel b c n (sf_encode phi).
Proof.
  intro HR. destruct (find_bounded_L (phi::A)) as [k Hk]. exists k. split.
  - apply (proj2 (source_bounded_sf_encode phi k)). apply Hk. now left.
  - apply (source_context_bound b c n A k HR). intros psi Hpsi. apply Hk. now right.
Qed.

Theorem source_context_branches_wf {ff} b c n (A:list(source_form_with ff)) phi psi theta :
  source_context_represents b c n A ->
  source_branches_wf natModel b c n (sf_encode phi) (sf_encode psi) (sf_encode theta).
Proof.
  intro HR. destruct (find_bounded_L (phi::psi::theta::A)) as [k Hk]. exists k.
  split; [apply (proj2 (source_bounded_sf_encode phi k));apply Hk;now left|].
  split; [apply (proj2 (source_bounded_sf_encode psi k));apply Hk;right;now left|].
  split; [apply (proj2 (source_bounded_sf_encode theta k));apply Hk;right;right;now left|].
  apply (source_context_bound b c n A k HR). intros eta Heta. apply Hk. right;right;now right.
Qed.

Theorem finite_source_renaming {ff} (phi:source_form_with ff) :
  forall b c n delta (sigma:nat->sf_term),
  (forall i, renaming_lookup natModel b c n delta i (sf_index (sigma i))) ->
  numerical_renaming natModel (sf_encode phi) b c n delta (sf_encode phi[sigma]).
Proof.
  induction phi as [|ff P t|ff op phi1 IHphi1 phi2 IHphi2|ff q phi IHphi]; intros b c n delta sigma Hmap.
  - apply numerical_renaming_invalid; [now left|reflexivity].
  - destruct P; change (Vector.t sf_term 2) in t; rewrite (rename_vector2_eta t); cbn [subst_form sf_encode Vector.map Vector.hd Vector.tl Vector.caseS Vector.caseS']; repeat rewrite rename_index_subst.
    + apply (proj2 (numerical_renaming_member natModel _ _ _ b c n delta _ (sf_make_graph _ _ _))).
      eexists; eexists. split; [apply Hmap|]. split; [apply Hmap|apply sf_make_graph].
    + apply (proj2 (numerical_renaming_equal natModel _ _ _ b c n delta _ (sf_make_graph _ _ _))).
      eexists; eexists. split; [apply Hmap|]. split; [apply Hmap|apply sf_make_graph].
  - cbn [subst_form sf_encode].
    destruct op.
    + apply (proj2 (numerical_renaming_binary natModel SFAnd _ _ _ b c n delta _
        (or_introl eq_refl) (sf_make_graph _ _ _))).
      eexists; eexists. split; [apply IHphi1;exact Hmap|].
      split; [apply IHphi2;exact Hmap|apply sf_make_graph].
    + apply (proj2 (numerical_renaming_binary natModel SFOr _ _ _ b c n delta _
        (or_intror (or_introl eq_refl)) (sf_make_graph _ _ _))).
      eexists; eexists. split; [apply IHphi1;exact Hmap|].
      split; [apply IHphi2;exact Hmap|apply sf_make_graph].
    + apply (proj2 (numerical_renaming_binary natModel SFImpl _ _ _ b c n delta _
        (or_intror (or_intror eq_refl)) (sf_make_graph _ _ _))).
      eexists; eexists. split; [apply IHphi1;exact Hmap|].
      split; [apply IHphi2;exact Hmap|apply sf_make_graph].
  - destruct (renaming_lift_total natModel b c n delta) as [d [e [m Hlift]]].
    assert (Hup : forall i, renaming_lookup natModel d e m delta i (sf_index (up sigma i))).
    { intros [|i]; rewrite source_up_substitution_index.
      - apply (proj2 (renaming_lift_head natModel b c n delta d e m 0 Hlift)). reflexivity.
      - apply (proj2 (renaming_lift_tail natModel b c n delta d e m i _ Hlift)). apply Hmap. }
    cbn [subst_form sf_encode]. destruct q.
    + apply (proj2 (numerical_renaming_quantifier natModel true _ _ b c n delta _ (sf_make_graph _ _ _))).
      exists d,e,m,(sf_encode phi[up sigma]). split; [exact Hlift|].
      split; [apply IHphi;exact Hup|apply sf_make_graph].
    + apply (proj2 (numerical_renaming_quantifier natModel false _ _ b c n delta _ (sf_make_graph _ _ _))).
      exists d,e,m,(sf_encode phi[up sigma]). split; [exact Hlift|].
      split; [apply IHphi;exact Hup|apply sf_make_graph].
Qed.




Theorem source_formula_shift_forward {ff} (phi:source_form_with ff) :
  source_formula_shift natModel (sf_encode phi) (sf_encode (subst_form ↑ phi)).
Proof.
  apply finite_source_renaming. intro i.
  apply (proj2 (context_shift_lookup natModel i (sf_index (↑ i)))). reflexivity.
Qed.

Theorem source_context_shift_represents {ff} b c n (A:list(source_form_with ff)) d e :
  source_context_represents b c n A -> context_shift natModel b c n d e ->
  source_context_represents d e n (List.map (subst_form ↑) A).
Proof.
  intros [En HA] HS. split; [now rewrite List.length_map|].
  intros i phi Hphi. rewrite List.nth_error_map in Hphi.
  assert (Hmap : forall (o : option (source_form_with ff)) phi,
    option_map (subst_form ↑) o = Some phi ->
    exists psi, o = Some psi /\ subst_form ↑ psi = phi).
  { intros [psi|] eta HE; cbn in HE; inversion HE; subst; eauto. }
  destruct (Hmap (List.nth_error A i) phi Hphi) as [psi [Hi HE]]. subst phi.
  assert (Hlt : coding_lt natModel i n).
  { apply sb_coding_lt_nat. rewrite En. apply List.nth_error_Some. rewrite Hi. discriminate. }
  destruct (beta_total natModel d e i) as [g Hg].
  pose proof (HS i (sf_encode psi) g Hlt (HA i psi Hi) Hg) as HR.
  assert (E : g = sf_encode (subst_form ↑ psi)).
  { exact (numerical_renaming_functional natModel (sf_encode psi) 0 0 0 1
      g (sf_encode (subst_form ↑ psi)) HR (source_formula_shift_forward psi)). }
  now rewrite <- E.
Qed.

Theorem source_instantiation_forward {ff} (phi:source_form_with ff) (t:sf_term) :
  numerical_instantiation natModel (sf_encode phi) (sf_index t)
    (sf_encode (subst_form (t .: var) phi)).
Proof.
  destruct (substitution_singleton_total natModel (sf_index t)) as [b [c [Hhead Htail]]].
  exists b,c. split; [exact Hhead|].
  apply (proj2 (standard_singleton_substitution_exact phi t b c _ Hhead)). reflexivity.
Qed.







