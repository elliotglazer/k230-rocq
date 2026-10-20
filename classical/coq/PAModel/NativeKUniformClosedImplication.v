(** A pure closed implication for both active-name cases. Its fixed
    Empty/Hosting background and canonical K-prime antecedent must all be
    relativized before using the implication inside an interpreted class. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetCodeDescent
  SourceBounded ZFCFiniteAxiomTemplates SourceNumeralLift SourceBoundedCalibration NumericalSetClosure NumericalContexts NumericalEnvironments
  NumericalSourceFull SourceSequents SourceClosedPrefixes SourceInstantiationConstructors
  SourceUniversalDistribution RawSourceImage RawSourcePrivateBound SourceRoleAbstraction
  SourceNativeKRecipes NativeKBundle NativeEqualCarrierBranches NativeEqualBackgroundCalibration
  NativeBundleUniformRoles SourceNamedProofRules.
From Undecidability.FOL Require Import Syntax.Bounded.
Unset Implicit Arguments.

Definition native_equal_background M background :=sf_relation M SFAnd
  (code_numeral M(sf_encode source_equal_empty))
  (code_numeral M(sf_encode source_equal_hosting)) background.

Lemma native_equal_background_closed M background :native_equal_background M background ->
  source_bounded M background (zeroM M).
Proof.
  intro HBG. apply(proj2(source_bounded_accept_binary M SFAnd
    (code_numeral M(sf_encode source_equal_empty))(code_numeral M(sf_encode source_equal_hosting))
    background (zeroM M)(or_introl eq_refl) HBG)). split.
  - apply(proj2(source_formula_numeral_bounded M source_equal_empty 0)).
    apply set_formula_boundb_sound. vm_compute. reflexivity.
  - apply(proj2(source_formula_numeral_bounded M source_equal_hosting 0)).
    apply set_formula_boundb_sound. vm_compute. reflexivity.
Qed.

Theorem native_kprime_uniform_closed_implication M a b private u phi abstract kprime closedK
    native n closedNative background inner out :
  private<>a ->private<>b ->raw_source_image M private phi ->
  source_role_abstraction M a b phi abstract ->source_kprime_core_recipe M abstract kprime ->
  all_prefix M private kprime closedK ->
  native_named_evaluation M (code_parameters a b private u) native_K_bundle_template native ->
  source_bounded M native n ->all_prefix M n native closedNative ->
  native_equal_background M background ->sf_relation M SFImpl closedK closedNative inner ->
  sf_relation M SFImpl background inner out ->
  source_full_prv M (zeroM M)(zeroM M)(zeroM M) out.
Proof.
  intros HPA HPB HDecode HAbstract HKprime HKPrefix HNative HNBound HNPrefix HBG HInner HOut.
  pose proof(source_role_abstraction_bounded M a b phi abstract private
    (raw_source_image_private_bound M private phi HDecode) HAbstract) as HAB.
  pose proof(source_kprime_core_recipe_bound M abstract kprime private HAB HKprime) as HKB.
  pose proof(all_prefix_closes M private kprime closedK HKB HKPrefix) as HKClosed.
  pose proof(all_prefix_closes M n native closedNative HNBound HNPrefix) as HNClosed.
  pose proof(native_equal_background_closed M background HBG) as HBGClosed.
  pose proof(proj2(source_bounded_accept_binary M SFImpl closedK closedNative inner (zeroM M)
    (or_intror(or_intror eq_refl)) HInner)(conj HKClosed HNClosed)) as HIClosed.
  destruct(environment_cons_total M (zeroM M)(zeroM M)(zeroM M) background) as(db&dc&dn&HD).
  assert(HDB:context_bounded M db dc dn (zeroM M)).
  { apply(proj2(context_bounded_cons M (zeroM M)(zeroM M)(zeroM M) background db dc dn (zeroM M) HD)).
    split;[exact HBGClosed|apply context_bounded_empty]. }
  destruct(environment_cons_total M db dc dn closedK) as(kb&kc&kn&HK).
  assert(HContext:context_bounded M kb kc kn (zeroM M)).
  { apply(proj2(context_bounded_cons M db dc dn closedK kb kc kn (zeroM M) HK));auto. }
  assert(PK:source_full_prv M kb kc kn closedK).
  { apply full_source_Ctx;[exists(zeroM M);auto|].
    apply(proj2(context_member_cons M db dc dn closedK kb kc kn closedK HK)). now left. }
  assert(PBG:source_full_prv M kb kc kn background).
  { apply full_source_Ctx;[exists(zeroM M);auto|].
    apply(proj2(context_member_cons M db dc dn closedK kb kc kn background HK)). right.
    apply(proj2(context_member_cons M (zeroM M)(zeroM M)(zeroM M) background db dc dn background HD)). now left. }
  assert(PE:source_full_prv M kb kc kn (code_numeral M(sf_encode source_equal_empty))).
  { apply(full_source_CE1 M kb kc kn (code_numeral M(sf_encode source_equal_empty))
      (code_numeral M(sf_encode source_equal_hosting)) background);[|exact PBG|exact HBG].
    exact(source_wf_binary_left M kb kc kn SFAnd _ _ background (or_introl eq_refl)
      HBG (source_full_prv_wellformed M kb kc kn background PBG)). }
  assert(PH:source_full_prv M kb kc kn (code_numeral M(sf_encode source_equal_hosting))).
  { apply(full_source_CE2 M kb kc kn (code_numeral M(sf_encode source_equal_empty))
      (code_numeral M(sf_encode source_equal_hosting)) background);[|exact PBG|exact HBG].
    exact(source_wf_binary_right M kb kc kn SFAnd _ _ background (or_introl eq_refl)
      HBG (source_full_prv_wellformed M kb kc kn background PBG)). }
  pose proof(source_full_prefix_eliminate M kb kc kn private kprime closedK HContext HKPrefix PK) as PKprime.
  pose proof(source_full_kprime_to_native_bundle M kb kc kn a b private u phi abstract kprime native
    HPA HPB HDecode HAbstract HKprime HNative PE PH PKprime) as PNative.
  pose proof(source_full_prefix_introduce M kb kc kn n native closedNative HContext HNPrefix PNative) as PClosed.
  apply(full_source_II M (zeroM M)(zeroM M)(zeroM M) background inner out db dc dn).
  - exists(zeroM M);split;[|apply context_bounded_empty].
    exact(proj2(source_bounded_accept_binary M SFImpl background inner out (zeroM M)
      (or_intror(or_intror eq_refl)) HOut)(conj HBGClosed HIClosed)).
  - apply(full_source_II M db dc dn closedK closedNative inner kb kc kn).
    + exists(zeroM M);auto.
    + exact PClosed.
    + exact HK.
    + exact HInner.
  - exact HD.
  - exact HOut.
Qed.

Print Assumptions native_kprime_uniform_closed_implication.
