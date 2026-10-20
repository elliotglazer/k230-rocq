(** Constructor inversion for the two actual substitutions in the finite
    canonical K scaffold. These lemmas do not assume their composition. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes SetCodeDescent
  NumericalSubstitutionMaps NumericalSubstitution SubstitutionPayloads SourceFiniteCutoffShift SourceNamedScopes SourceFiniteMapLifts.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma source_double_binary_inv M h x y f b c n base d e m tail first out :
  sf_binary h ->sf_relation M h x y f ->
  numerical_substitution M f b c n base first ->numerical_substitution M first d e m tail out ->
  exists x1 y1 x2 y2,numerical_substitution M x b c n base x1 /\
    numerical_substitution M y b c n base y1 /\
    numerical_substitution M x1 d e m tail x2 /\numerical_substitution M y1 d e m tail y2 /\
    sf_relation M h x2 y2 out.
Proof.
  intros HH HF H1 H2.
  destruct (proj1 (numerical_substitution_binary M h x y f b c n base first HH HF) H1)
    as (x1&y1&HX&HY&HFirst).
  destruct (proj1 (numerical_substitution_binary M h x1 y1 first d e m tail out HH HFirst) H2)
    as (x2&y2&HXA&HYA&HOut).
  exists x1,y1,x2,y2. repeat first [assumption|split].
Qed.

Lemma source_double_quantifier_inv M universal body f b c n base d e m tail first out :
  sf_relation M (substitution_source_quantifier universal) body (zeroM M) f ->
  numerical_substitution M f b c n base first ->numerical_substitution M first d e m tail out ->
  exists nb nc nn nd ne nm body1 body2,
    substitution_lift M b c n base nb nc nn /\substitution_lift M d e m tail nd ne nm /\
    numerical_substitution M body nb nc nn (succM M base) body1 /\
    numerical_substitution M body1 nd ne nm (succM M tail) body2 /\
    sf_relation M (substitution_source_quantifier universal) body2 (zeroM M) out.
Proof.
  intros HF H1 H2.
  destruct (proj1 (numerical_substitution_quantifier M universal body f b c n base first HF) H1)
    as (nb&nc&nn&body1&HL1&HS1&HFirst).
  destruct (proj1 (numerical_substitution_quantifier M universal body1 first d e m tail out HFirst) H2)
    as (nd&ne&nm&body2&HL2&HS2&HOut).
  exists nb,nc,nn,nd,ne,nm,body1,body2. repeat first [assumption|split].
Qed.

Lemma source_double_fixed_atom M equality i j atom first out depth cb cc cn sb sc db dc dn :
  (i<depth)%nat ->(j<depth)%nat ->
  sf_relation M (substitution_source_atom equality) (code_numeral M i) (code_numeral M j) atom ->
  source_cutoff_shift_map M depth cb cc cn ->
  source_substitution_lifts M depth sb sc (code_numeral M 2) (zeroM M) db dc dn ->
  numerical_substitution M atom cb cc cn (code_numeral M (S depth)) first ->
  numerical_substitution M first db dc dn (code_numeral M depth) out ->
  sf_relation M (substitution_source_atom equality) (code_numeral M i) (code_numeral M j) out.
Proof.
  intros HI HJ HA HC HL H1 H2.
  destruct (proj1 (numerical_substitution_atom M equality _ _ atom cb cc cn _ first HA) H1)
    as (i1&j1&HI1&HJ1&HFirst).
  pose proof (substitution_lookup_functional M _ _ _ _ _ i1 _ HI1
    (source_cutoff_shift_head M depth cb cc cn i HI HC)) as EI1. subst i1.
  pose proof (substitution_lookup_functional M _ _ _ _ _ j1 _ HJ1
    (source_cutoff_shift_head M depth cb cc cn j HJ HC)) as EJ1. subst j1.
  destruct (proj1 (numerical_substitution_atom M equality _ _ first db dc dn _ out HFirst) H2)
    as (i2&j2&HI2&HJ2&HOut).
  pose proof (source_substitution_lifts_head M depth sb sc (code_numeral M 2) (zeroM M) db dc dn i HI HL) as HLI.
  pose proof (source_substitution_lifts_head M depth sb sc (code_numeral M 2) (zeroM M) db dc dn j HJ HL) as HLJ.
  rewrite named_scope_succ_zero in HLI,HLJ.
  pose proof (substitution_lookup_functional M _ _ _ _ _ i2 _ HI2 HLI) as EI2. subst i2.
  pose proof (substitution_lookup_functional M _ _ _ _ _ j2 _ HJ2 HLJ) as EJ2. now subst j2.
Qed.

Print Assumptions source_double_fixed_atom.
