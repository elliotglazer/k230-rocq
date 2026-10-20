(** Reinsert the genuine L-domain guard into the bounded existential
 supplied by a reflected request. Witnesses are preserved by actual ExE/ExI. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming NumericalSourceFull
 SourceConjunctionRules SourceDerivedRules SourceQuantifierRules SourceUniversalPropositional
 SourceContextProofHelpers SourceExistentialMap.
Unset Implicit Arguments.
Theorem source_full_exists_add_domain_guard M cb cc cn k member domain matrix oldBody oldEx point all newBody newEx:
 context_bounded M cb cc cn k ->source_bounded M member(succM M k) ->source_bounded M domain(succM M k) ->
 source_bounded M matrix(succM M k) ->sf_relation M SFAnd member matrix oldBody ->sf_relation M SFEx oldBody(zeroM M)oldEx ->
 sf_relation M SFImpl member domain point ->sf_relation M SFAll point(zeroM M)all ->
 sf_relation M SFAnd domain oldBody newBody ->sf_relation M SFEx newBody(zeroM M)newEx ->
 source_full_prv M cb cc cn all ->source_full_prv M cb cc cn oldEx ->source_full_prv M cb cc cn newEx.
Proof.
 intros BC BM BD BA HB HO HP HAll HNewBody HNewEx PAll POld.
 pose proof(proj2(source_bounded_accept_binary M SFAnd member matrix oldBody(succM M k)(or_introl eq_refl)HB)(conj BM BA))as BBody.
 pose proof(proj2(source_bounded_accept_binary M SFAnd domain oldBody newBody(succM M k)(or_introl eq_refl)HNewBody)(conj BD BBody))as BNewBody.
 pose proof(proj2(source_bounded_accept_unary M SFEx newBody newEx k(or_intror eq_refl)HNewEx)BNewBody)as BNew.
 destruct(context_shift_total M cb cc cn)as(sb&sc&HShift).
 pose proof(source_full_all_shift M cb cc cn point all sb sc HAll PAll HShift)as PPoint.
 destruct(environment_cons_total M sb sc cn oldBody)as(ub&uc&un&HCons).
 pose proof(proj2(context_bounded_cons M sb sc cn oldBody ub uc un(succM M k)HCons)
  (conj BBody(context_shift_preserves_bound M cb cc cn sb sc k HShift BC)))as BU.
 pose proof(source_full_cons_head M sb sc cn oldBody ub uc un(succM M k)HCons BBody BU)as PBody.
 pose proof(source_full_conjunction_left M ub uc un member matrix oldBody HB PBody)as PMember.
 pose proof(source_full_cons_weaken M sb sc cn oldBody ub uc un(succM M k)point HCons BU PPoint)as PPoint'.
 pose proof(source_full_modus_ponens M ub uc un member domain point HP PPoint' PMember)as PDomain.
 pose proof(full_source_CI M ub uc un domain oldBody newBody(ex_intro _ (succM M k)(conj BNewBody BU))PDomain PBody HNewBody)as PNewBody.
 destruct(numerical_renaming_total M newEx(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(shifted&HS).
 exact(source_full_exists_map M cb cc cn oldBody newBody oldEx newEx sb sc ub uc un shifted
  (ex_intro _ k(conj BNew BC))HO HNewEx HShift HCons HS POld PNewBody).
Qed.
Theorem source_full_reflected_request_add_domain_guard M cb cc cn k member domain matrix oldBody oldEx point all newBody newEx some request guardedRequest:
 context_bounded M cb cc cn k ->source_bounded M member(succM M k) ->source_bounded M domain(succM M k) ->
 source_bounded M matrix(succM M k) ->source_bounded M some k ->
 sf_relation M SFAnd member matrix oldBody ->sf_relation M SFEx oldBody(zeroM M)oldEx ->
 sf_relation M SFImpl member domain point ->sf_relation M SFAll point(zeroM M)all ->
 sf_relation M SFAnd domain oldBody newBody ->sf_relation M SFEx newBody(zeroM M)newEx ->
 sf_relation M SFImpl some oldEx request ->sf_relation M SFImpl some newEx guardedRequest ->
 source_full_prv M cb cc cn all ->source_full_prv M cb cc cn request ->source_full_prv M cb cc cn guardedRequest.
Proof.
 intros BC BM BD BA BSome HB HO HP HAll HNewBody HNewEx HRequest HGuarded PAll PRequest.
 pose proof(proj2(source_bounded_accept_binary M SFAnd member matrix oldBody(succM M k)(or_introl eq_refl)HB)(conj BM BA))as BBody.
 pose proof(proj2(source_bounded_accept_binary M SFAnd domain oldBody newBody(succM M k)(or_introl eq_refl)HNewBody)(conj BD BBody))as BNewBody.
 pose proof(proj2(source_bounded_accept_unary M SFEx newBody newEx k(or_intror eq_refl)HNewEx)BNewBody)as BNew.
 pose proof(proj2(source_bounded_accept_binary M SFImpl some newEx guardedRequest k(or_intror(or_intror eq_refl))HGuarded)(conj BSome BNew))as BTarget.
 destruct(environment_cons_total M cb cc cn some)as(ub&uc&un&HCons).
 pose proof(proj2(context_bounded_cons M cb cc cn some ub uc un k HCons)(conj BSome BC))as BU.
 pose proof(source_full_cons_head M cb cc cn some ub uc un k HCons BSome BU)as PSome.
 pose proof(source_full_cons_weaken M cb cc cn some ub uc un k request HCons BU PRequest)as PR.
 pose proof(source_full_cons_weaken M cb cc cn some ub uc un k all HCons BU PAll)as PA.
 pose proof(source_full_modus_ponens M ub uc un some oldEx request HRequest PR PSome)as POld.
 apply(full_source_II M cb cc cn some newEx guardedRequest ub uc un(ex_intro _ k(conj BTarget BC))).
 - exact(source_full_exists_add_domain_guard M ub uc un k member domain matrix oldBody oldEx point all newBody newEx
    BU BM BD BA HB HO HP HAll HNewBody HNewEx PA POld).
 - exact HCons.
 - exact HGuarded.
Qed.
Print Assumptions source_full_exists_add_domain_guard.
Print Assumptions source_full_reflected_request_add_domain_guard.
