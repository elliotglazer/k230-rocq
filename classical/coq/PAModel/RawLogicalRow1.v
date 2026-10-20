(** The encoded existential-equality row has an actual source ZFC proof.
    Closing and reopening its named binder may move raw code1 to any
    diagonal membership atom; Foundation refutes that atom uniformly. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions CodeDescent Pairing
  NumericalProofs ProofTemplates NumericalEquality SetFormulaCodes SetCodeDescent
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
  NumericalInstantiation NumericalContexts SourceSequents RawBinderRenaming RawBinderInstantiation
  RawSourceImage RawSourceImageInversion RawSourceImageBounds RawEqualityCalibration
  SourceZFCProvability SourceZFCReflexivity SourceZFCNoSelf SourceUniversalRefutation.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma raw_one_membership_graph M :
  membership_graph M (zeroM M) (zeroM M) (code_numeral M 1).
Proof.
  exists (zeroM M). split;[apply pair_zero|].
  rewrite Arithmetic.mul_comm,Arithmetic.mul_zero,coding_add_zero. reflexivity.
Qed.

Theorem raw_exists_equality_graph_source M a b eq neg quantified raw out :
  equality_graph M a b eq -> implication_graph M eq (code_numeral M 1) neg ->
  universal_graph M a neg quantified ->
  implication_graph M quantified (code_numeral M 1) raw ->
  raw_source_image M raw out -> source_zfc_provable M out.
Proof.
  intros HE HN HQ HR HO.
  pose proof (raw_positive_tag_nonzero M 1 (zeroM M) (zeroM M) (code_numeral M 1)
    ltac:(lia) (raw_one_membership_graph M)) as HOneN.
  pose proof (raw_implication_nonzero_consequent M eq (code_numeral M 1) neg HOneN HN) as HNegN.
  pose proof (raw_implication_nonzero_consequent M quantified (code_numeral M 1) raw HOneN HR) as HRawN.
  destruct (raw_source_implication_inv M quantified (code_numeral M 1) raw out HRawN HR HO)
    as (sq&bad0&HQI&HBad0I&HSOut).
  destruct (raw_source_universal_inv M a neg quantified sq HQ HQI)
    as (sneg&rb&rc&matrix&HNI&HMap&HRename&HSQ).
  destruct (raw_source_implication_inv M eq (code_numeral M 1) neg sneg HNegN HN HNI)
    as (seq&sbad&HEI&HBadI&HSNeg).
  pose proof (raw_source_equal_inv M a b eq seq HE HEI) as HSEq.
  pose proof (raw_one_source_member M sbad HBadI) as HSBad.
  apply (proj1 (numerical_renaming_binary M SFImpl seq sbad sneg rb rc
    (succM M a) (succM M (zeroM M)) matrix ltac:(unfold sf_binary;auto) HSNeg)) in HRename.
  destruct HRename as (req&rbd&HRE&HRB&HRImpl).
  apply (proj1 (numerical_renaming_equal M a b seq rb rc (succM M a)
    (succM M (zeroM M)) req HSEq)) in HRE.
  destruct HRE as (ai&bi&HA&HB&HREq).
  apply (proj1 (numerical_renaming_member M (zeroM M) (zeroM M) sbad rb rc
    (succM M a) (succM M (zeroM M)) rbd HSBad)) in HRB.
  destruct HRB as (di&di'&HD&HD'&HRBad).
  assert (ED:di'=di).
  { exact (renaming_lookup_functional M rb rc (succM M a) (succM M (zeroM M))
      (zeroM M) di' di HD' HD). }
  subst di'.
  destruct (numerical_instantiation_total M matrix b) as (instance&HInst).
  destruct HInst as (sb&sc&HHead&HSub).
  apply (proj1 (numerical_substitution_binary M SFImpl req rbd matrix sb sc
    (succM M (zeroM M)) (zeroM M) instance ltac:(unfold sf_binary;auto) HRImpl)) in HSub.
  destruct HSub as (ieq&ibad&HIE&HIB&HSInst).
  apply (proj1 (numerical_substitution_equal M ai bi req sb sc
    (succM M (zeroM M)) (zeroM M) ieq HREq)) in HIE.
  destruct HIE as (aa&bb&HAA&HBB&HIEq).
  assert (EAA:aa=b).
  { exact (raw_binder_instantiation_bound_name M a b rb rc sb sc ai aa HMap HHead HA HAA). }
  assert (EBB:bb=b).
  { exact (raw_binder_instantiation_witness_name M a b rb rc sb sc bi bb HMap HHead HB HBB). }
  subst aa bb.
  apply (proj1 (numerical_substitution_member M di di rbd sb sc
    (succM M (zeroM M)) (zeroM M) ibad HRBad)) in HIB.
  destruct HIB as (dd&dd'&HDD&HDD'&HIBad).
  assert (EDD:dd'=dd).
  { exact (substitution_lookup_functional M sb sc (succM M (zeroM M)) (zeroM M)
      di dd' dd HDD' HDD). }
  subst dd'.
  destruct (sf_relation_total M SFImpl ibad (zeroM M)) as (notbad&HNotBad).
  apply (source_zfc_universal_refutation M ieq ibad notbad matrix sq instance b bad0 out).
  - exact (source_zfc_reflexivity M b ieq HIEq).
  - exact (source_zfc_no_self M dd ibad notbad HIBad HNotBad).
  - exact HNotBad.
  - exact HSQ.
  - exists sb,sc. split;[exact HHead|].
    apply (proj2 (numerical_substitution_binary M SFImpl req rbd matrix sb sc
      (succM M (zeroM M)) (zeroM M) instance ltac:(unfold sf_binary;auto) HRImpl)).
    exists ieq,ibad. split.
    + apply (proj2 (numerical_substitution_equal M ai bi req sb sc
        (succM M (zeroM M)) (zeroM M) ieq HREq)). exists b,b. auto.
    + split;[|exact HSInst].
      apply (proj2 (numerical_substitution_member M di di rbd sb sc
        (succM M (zeroM M)) (zeroM M) ibad HRBad)). exists dd,dd. auto.
  - exact HSInst.
  - exact HSOut.
  - destruct (raw_source_image_bounded M raw out HO) as (k&HK).
    exists k. split;[exact HK|apply context_bounded_empty].
Qed.

Theorem source_zfc_raw_row1 M env raw out :
  code_relation M env code_row1 raw -> raw_source_image M raw out -> source_zfc_provable M out.
Proof.
  intros HR HO.
  destruct (code_relation_total M (E_weq (CEvar 0) (CEvar 1)) env) as (eq&HE).
  destruct (code_relation_total M (E_wn (E_weq (CEvar 0) (CEvar 1))) env) as (neg&HN).
  destruct (code_relation_total M (E_wal (CEvar 0) (E_wn (E_weq (CEvar 0) (CEvar 1)))) env)
    as (quantified&HQ).
  apply (raw_exists_equality_graph_source M (env 0) (env 1) eq neg quantified raw out).
  - exact (proj1 (expression_equality_graph M env (CEvar 0) (CEvar 1) _ _ eq eq_refl eq_refl) HE).
  - exact (expression_implication_graph M env (E_weq (CEvar 0) (CEvar 1)) (CEconst 1)
      eq (code_numeral M 1) neg HE eq_refl HN).
  - exact (expression_universal_graph M env (CEvar 0) (E_wn (E_weq (CEvar 0) (CEvar 1)))
      _ neg quantified eq_refl HN HQ).
  - exact (expression_implication_graph M env
      (E_wal (CEvar 0) (E_wn (E_weq (CEvar 0) (CEvar 1)))) (CEconst 1)
      quantified (code_numeral M 1) raw HQ eq_refl HR).
  - exact HO.
Qed.

Print Assumptions raw_exists_equality_graph_source.
Print Assumptions source_zfc_raw_row1.
