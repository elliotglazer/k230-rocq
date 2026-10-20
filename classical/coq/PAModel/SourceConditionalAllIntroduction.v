(** An actual closed-theory derivation of a shifted conditional matrix
    gives the unshifted condition followed by a universal conclusion. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceTraceBounds NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull SourceQuantifierRules
  SourceProofWeakening SourceClosedContextShift SourceImplicationAllShift SourceContextProofHelpers SourceLeastOrdinalWitness
  SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.

Theorem source_descriptor_conditional_all_introduction M T p ps a all point result k:
  source_bounded M p k ->source_bounded M a(succM M k) ->source_formula_shift M p ps ->
  sf_relation M SFAll a(zeroM M)all ->sf_relation M SFImpl ps a point ->sf_relation M SFImpl p all result ->
  source_descriptor_provable M T point ->source_descriptor_provable M T result.
Proof.
  intros BP BA HS HA HP HR(b&c&n&HCtx&PPoint).
  pose proof(source_shift_bound M p ps k BP HS) as BPS.
  pose proof(proj2(source_bounded_accept_unary M SFAll a all k(or_introl eq_refl)HA)BA) as BAll.
  pose proof(proj2(source_bounded_accept_binary M SFImpl p all result k(or_intror(or_intror eq_refl))HR)(conj BP BAll)) as BResult.
  pose proof(context_bounded_monotone M b c n(zeroM M)k(proj1 HCtx)(coding_zero_lt_succ M k)) as BCtx.
  destruct(environment_cons_total M b c n p) as(ub&uc&un&HCons).
  pose proof(proj2(context_bounded_cons M b c n p ub uc un k HCons)(conj BP BCtx)) as BNew.
  destruct(environment_cons_total M b c n ps) as(vb&vc&vn&HConsShift).
  assert(E:vn=un) by(rewrite(proj1 HConsShift),(proj1 HCons);reflexivity). subst vn.
  pose proof(context_renaming_cons M b c n(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)b c p ps ub uc un vb vc
    (source_closed_context_shift_self M b c n(proj1 HCtx))HS HCons HConsShift) as HShiftContext.
  pose proof(context_shift_preserves_bound M ub uc un vb vc k HShiftContext BNew) as BShiftContext.
  assert(PA:source_full_prv M vb vc un a).
  { apply(full_source_IE M vb vc un ps a point);[exists(succM M k);auto| | |exact HP].
    - exact(source_full_cons_weaken M b c n ps vb vc un(succM M k)point HConsShift BShiftContext PPoint).
    - exact(source_full_cons_head M b c n ps vb vc un(succM M k)HConsShift BPS BShiftContext). }
  assert(PAll:source_full_prv M ub uc un all).
  { exact(full_source_AllI M ub uc un a all vb vc(ex_intro _ k(conj BAll BNew))PA HShiftContext HA). }
  exists b,c,n. split;[exact HCtx|].
  exact(full_source_II M b c n p all result ub uc un(ex_intro _ k(conj BResult BCtx))PAll HCons HR).
Qed.

Theorem source_zfr_conditional_all_introduction M p ps a all point result k:
  source_bounded M p k ->source_bounded M a(succM M k) ->source_formula_shift M p ps ->
  sf_relation M SFAll a(zeroM M)all ->sf_relation M SFImpl ps a point ->sf_relation M SFImpl p all result ->
  source_zfr_provable M point ->source_zfr_provable M result.
Proof.
  intros BP BA HS HA HP HR PP. apply(proj1(source_zfr_descriptor_provable M result)).
  exact(source_descriptor_conditional_all_introduction M ZFRSourceDescriptor p ps a all point result k BP BA HS HA HP HR
    (proj2(source_zfr_descriptor_provable M point)PP)).
Qed.

Print Assumptions source_descriptor_conditional_all_introduction.
Print Assumptions source_zfr_conditional_all_introduction.
