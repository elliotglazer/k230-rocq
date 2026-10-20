(** Closing one named variable and substituting a witness for the new
    de Bruijn variable implements the expected free-name replacement. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalRenamingMaps
  NumericalSubstitutionMaps SubstitutionSource NumericalInstantiation RawBinderRenaming.
Unset Implicit Arguments.

Theorem raw_binder_instantiation_lookup M x witness rb rc sb sc i u v :
  raw_binder_renaming M x rb rc ->
  substitution_lookup M sb sc (succM M (zeroM M)) (zeroM M) (zeroM M) witness ->
  renaming_lookup M rb rc (succM M x) (succM M (zeroM M)) i u ->
  substitution_lookup M sb sc (succM M (zeroM M)) (zeroM M) u v ->
  (i=x /\ v=witness) \/ (i<>x /\ v=i).
Proof.
  intros HMap HHead HI HU. apply (proj1 (HMap i u)) in HI.
  destruct HI as [[E ->]|[NE ->]].
  - left. split;[exact E|]. exact (substitution_lookup_functional M _ _ _ _ (zeroM M) v witness HU HHead).
  - right. split;[exact NE|].
    exact (substitution_lookup_functional M _ _ _ _ (succM M i) v i HU
      (substitution_singleton_tail M sb sc i)).
Qed.

Corollary raw_binder_instantiation_bound_name M x witness rb rc sb sc u v :
  raw_binder_renaming M x rb rc ->
  substitution_lookup M sb sc (succM M (zeroM M)) (zeroM M) (zeroM M) witness ->
  renaming_lookup M rb rc (succM M x) (succM M (zeroM M)) x u ->
  substitution_lookup M sb sc (succM M (zeroM M)) (zeroM M) u v -> v=witness.
Proof.
  intros HM HH HR HS. destruct (raw_binder_instantiation_lookup M x witness rb rc sb sc x u v HM HH HR HS)
    as [[_ E]|[NE _]];[exact E|contradiction].
Qed.

Corollary raw_binder_instantiation_witness_name M x witness rb rc sb sc u v :
  raw_binder_renaming M x rb rc ->
  substitution_lookup M sb sc (succM M (zeroM M)) (zeroM M) (zeroM M) witness ->
  renaming_lookup M rb rc (succM M x) (succM M (zeroM M)) witness u ->
  substitution_lookup M sb sc (succM M (zeroM M)) (zeroM M) u v -> v=witness.
Proof.
  intros HM HH HR HS. destruct (raw_binder_instantiation_lookup M x witness rb rc sb sc witness u v HM HH HR HS)
    as [[_ E]|[_ E]];exact E.
Qed.

Print Assumptions raw_binder_instantiation_lookup.
