(** Actual witness-preserving monotonicity of bounded existential formulas.
    The matrix is an arbitrary internal source code; every branch is built. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalEnvironments NumericalRenaming NumericalContextRenaming
  NumericalSourceFull SourceRawSubset SourceQuantifierRules SourceConjunctionRules
  SourceInstantiationConstructors SourceContextProofHelpers SourceProofRenaming SourceExistentialMap.
Unset Implicit Arguments.

Theorem source_full_bounded_exists_monotone M cb cc cn k x y matrix subset
    left right bodyX bodyY exX exY :
  context_bounded M cb cc cn k ->source_bounded M matrix (succM M k) ->
  coding_lt M x k ->coding_lt M y k ->source_raw_subset_graph M x y subset ->
  sf_relation M SFMember (zeroM M) (succM M x) left ->
  sf_relation M SFMember (zeroM M) (succM M y) right ->
  sf_relation M SFAnd left matrix bodyX ->sf_relation M SFAnd right matrix bodyY ->
  sf_relation M SFEx bodyX (zeroM M) exX ->sf_relation M SFEx bodyY (zeroM M) exY ->
  source_full_prv M cb cc cn subset ->source_full_prv M cb cc cn exX ->
  source_full_prv M cb cc cn exY.
Proof.
  intros HC HM HX HY HS HL HR HBX HBY HEX HEY PS PX.
  assert (HAtom:forall z a,coding_lt M z k ->sf_relation M SFMember (zeroM M) (succM M z) a ->
    source_bounded M a (succM M k)).
  { intros z a HZ HA. apply (proj2(source_bounded_accept_atom M SFMember _ _ a
      (succM M k) (or_introl eq_refl) HA)).
    split;[apply coding_zero_lt_succ|apply (proj2(coding_lt_succ_cancel M z k)),HZ]. }
  assert (HBodyX:source_bounded M bodyX (succM M k)).
  { apply (proj2(source_bounded_accept_binary M SFAnd left matrix bodyX (succM M k)
      (or_introl eq_refl) HBX)). split;[exact(HAtom x left HX HL)|exact HM]. }
  assert (HBodyY:source_bounded M bodyY (succM M k)).
  { apply (proj2(source_bounded_accept_binary M SFAnd right matrix bodyY (succM M k)
      (or_introl eq_refl) HBY)). split;[exact(HAtom y right HY HR)|exact HM]. }
  assert (HExY:source_bounded M exY k).
  { exact(proj2(source_bounded_accept_unary M SFEx bodyY exY k (or_intror eq_refl) HEY) HBodyY). }
  destruct (context_shift_total M cb cc cn) as (sb&sc&HShift).
  destruct (environment_cons_total M sb sc cn bodyX) as (ub&uc&un&HCons).
  assert (HBranch:context_bounded M ub uc un (succM M k)).
  { apply (proj2(context_bounded_cons M sb sc cn bodyX ub uc un (succM M k) HCons)).
    split;[exact HBodyX|exact(context_shift_preserves_bound M cb cc cn sb sc k HShift HC)]. }
  destruct (numerical_renaming_total M subset (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))
    as (subset'&HSubsetShift).
  pose proof (source_raw_subset_shift M x y subset subset' HS HSubsetShift) as HS'.
  assert (PS':source_full_prv M ub uc un subset').
  { apply (source_full_cons_weaken M sb sc cn bodyX ub uc un (succM M k) subset' HCons HBranch).
    exact(source_full_prv_renaming M cb cc cn subset (zeroM M)(zeroM M)(zeroM M)
      (code_numeral M 1) sb sc subset' PS HShift HSubsetShift). }
  pose proof (source_full_cons_head M sb sc cn bodyX ub uc un (succM M k) HCons HBodyX HBranch) as PBX.
  pose proof (source_full_conjunction_left M ub uc un left matrix bodyX HBX PBX) as PL.
  pose proof (source_full_conjunction_right M ub uc un left matrix bodyX HBX PBX) as PM.
  pose proof (source_full_raw_subset_member M ub uc un (succM M x)(succM M y)(zeroM M)
    subset' left right HS' HL HR PS' PL) as PR.
  assert (PBY:source_full_prv M ub uc un bodyY).
  { apply (full_source_CI M ub uc un right matrix bodyY);[|exact PR|exact PM|exact HBY].
    exact(source_wf_binary M ub uc un SFAnd right matrix bodyY (or_introl eq_refl) HBY
      (source_full_prv_wellformed M ub uc un right PR)
      (source_full_prv_wellformed M ub uc un matrix PM)). }
  destruct (numerical_renaming_total M exY (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))
    as (shifted&HExShift).
  exact(source_full_exists_map M cb cc cn bodyX bodyY exX exY sb sc ub uc un shifted
    (ex_intro _ k (conj HExY HC)) HEX HEY HShift HCons HExShift PX PBY).
Qed.

Print Assumptions source_full_bounded_exists_monotone.
