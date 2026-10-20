(** Both quantified cases of the uniform numerical TV induction.
    The only induction premise is the actual child TV property. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes
  SourceBounded SourceBoundMonotone NumericalContexts NumericalEnvironments NumericalSourceFull
  SourceContextProofHelpers SourceRelativizationRules SourceRelativization SourceRelativizationFunctionality
  SourceRelativizationBounds SourceSetRelativizationRules SourceSetRelativization SourceSetRelativizationFunctionality
  SourceSetRelativizationBounds SourceIffGraphs SourcePCSPieces SourceQuantifierPieces SourceQuantifierPieceInversion
  SourcePieceWitnessInstance SourcePieceWitnessUnroll SourceEwAtSyntax SourceEwMonotone
  SourceTarskiVaughtInputs SourceTarskiVaughtInvariant SourceTarskiVaughtChild SourceTarskiVaughtExists SourceTarskiVaughtAllPositive.
Unset Implicit Arguments.

Theorem source_full_tv_piece_witness M domain phi count body piece carrier ew cb cc cn k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
  source_quantifier_body M phi count count body ->source_pcs_sign M domain body piece ->
  source_ew_at M domain piece carrier ew ->context_bounded M cb cc cn k ->
  coding_lt M count(succM M k) ->coding_lt M carrier k ->source_tv_members M cb cc cn count carrier ->
  source_tv_witnesses M domain phi count carrier cb cc cn ->source_full_prv M cb cc cn ew.
Proof.
  intros HD HF HB HS HE BC HC HY HM HW.
  pose proof(source_pcs_sign_bounded M domain body piece(succM M count)HD
    (source_quantifier_body_bounded M phi count count body HB HF)HS)as BP.
  destruct(source_piece_witness_instance_total M domain count piece carrier)as(out&HO).
  exact(source_full_piece_witness_instance_elimination M domain count piece carrier out ew cb cc cn k
    HD BP BC HC HY HO HE(HW count body piece out HB HS HO)HM).
Qed.

Theorem source_tv_quantifier M(universal:bool)body phi:
  sf_relation M(sr_source_quantifier universal)body(zeroM M)phi ->source_tv_at M body ->source_tv_at M phi.
Proof.
  intros HShape IH domain count carrier left right equiv cb cc cn k HD HF BC HC HY HL HR HE HM HW HS.
  assert(HH:sr_source_quantifier universal=SFAll \/sr_source_quantifier universal=SFEx).
  { destruct universal;unfold sr_source_quantifier;auto. }
  assert(HB:source_bounded M body(succM M count)).
  { destruct universal.
    - exact(proj1(source_bounded_accept_unary M SFAll body phi count(or_introl eq_refl)HShape)HF).
    - exact(proj1(source_bounded_accept_unary M SFEx body phi count(or_intror eq_refl)HShape)HF). }
  assert(HTop:source_quantifier_body M phi count count body).
  { apply source_quantifier_body_top. destruct universal;[left|right];exact HShape. }
  assert(HChild:source_tv_witnesses M domain body(succM M count)carrier cb cc cn).
  { intros pc b p out HB' HP' HO. apply(HW pc b p out);[|exact HP'|exact HO].
    apply(proj2(source_quantifier_body_quantifier M(sr_source_quantifier universal)body phi count pc b HH HShape)). now right. }
  destruct(source_relativization_quantifier_inv M domain universal body phi left HShape HL)as(a&HA&HLeft).
  destruct(source_set_relativization_quantifier_inv M carrier universal body phi right HShape HR)as(b&HB'&HRight).
  destruct HRight as(guard&mid&HG&HMid&HQRight).
  assert(HRight:sr_quantifier M universal guard b right).
  { exists mid. auto. }
  destruct(source_iff_total M a b)as(childEquiv&HChildEquiv).
  destruct(sf_relation_total M SFImpl guard childEquiv)as(point&HPoint).
  destruct(sf_relation_total M SFAll point(zeroM M))as(all&HAll).
  pose proof(source_full_tv_guarded_child M body domain count carrier a b childEquiv guard point all cb cc cn k
    IH HD HB BC HC HY HA HB' HChildEquiv HG HPoint HAll HM HChild HS)as PAll.
  destruct HS as(subset&(guard'&subsetPoint&HGuard'&HSubsetPoint&HSubset)&PSubset).
  assert(EGuard:guard'=guard)by(eapply sf_relation_functional;eassumption). subst guard'.
  pose proof(source_bounded_monotone M phi count k HF HC)as BF.
  pose proof(source_relativization_preserves_bound M phi domain k left HD BF HL)as BL.
  pose proof(source_set_relativization_preserves_bound M phi carrier k right HY BF HR)as BR.
  pose proof(source_iff_bounded M left right equiv k BL BR HE)as BE.
  pose proof(source_bounded_monotone M body(succM M count)(succM M k)HB
    (proj2(coding_lt_succ_cancel M count(succM M k))HC))as BB.
  pose proof(source_relativization_preserves_bound M body domain(succM M k)a HD BB HA)as BA.
  pose proof(source_set_relativization_preserves_bound M body(succM M carrier)(succM M k)b
    (proj2(coding_lt_succ_cancel M carrier k)HY)BB HB')as BB'.
  assert(BGuard:source_bounded M guard(succM M k)).
  { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M carrier)guard(succM M k)(or_introl eq_refl)HG)).
    split;[apply coding_zero_lt_succ|exact(proj2(coding_lt_succ_cancel M carrier k)HY)]. }
  destruct(sf_relation_total M SFImpl a(zeroM M))as(negA&HNegA).
  set(piece:=if universal then negA else a).
  assert(HSign:source_pcs_sign M domain body piece).
  { unfold piece. destruct universal;[right;exists a;auto|now left]. }
  destruct(source_ew_at_total M domain piece carrier)as(closure&HClosure).
  pose proof(source_full_tv_piece_witness M domain phi count body piece carrier closure cb cc cn k
    HD HF HTop HSign HClosure BC HC HY HM HW)as PClosure.
  destruct HClosure as(guard'&exD&exA&HClosureGuard&HExD&HExA&HClosure).
  assert(EGuard:guard'=guard)by(eapply sf_relation_functional;eassumption). subst guard'.
  destruct(source_iff_parts M left right equiv HE)as(lr&rl&HLR&HRL&HAnd).
  pose proof(proj2(source_bounded_accept_binary M SFImpl left right lr k(or_intror(or_intror eq_refl))HLR)(conj BL BR))as BLR.
  pose proof(proj2(source_bounded_accept_binary M SFImpl right left rl k(or_intror(or_intror eq_refl))HRL)(conj BR BL))as BRL.
  destruct(environment_cons_total M cb cc cn left)as(lb&lc&ln&HConsL).
  pose proof(proj2(context_bounded_cons M cb cc cn left lb lc ln k HConsL)(conj BL BC))as BConsL.
  pose proof(source_full_cons_head M cb cc cn left lb lc ln k HConsL BL BConsL)as PL.
  pose proof(source_full_cons_weaken M cb cc cn left lb lc ln k all HConsL BConsL PAll)as PAllL.
  pose proof(source_full_cons_weaken M cb cc cn left lb lc ln k subset HConsL BConsL PSubset)as PSubsetL.
  pose proof(source_full_cons_weaken M cb cc cn left lb lc ln k closure HConsL BConsL PClosure)as PClosureL.
  assert(PR:source_full_prv M lb lc ln right).
  { destruct universal.
    - exact(source_full_tv_all_forward_from_positive M lb lc ln domain guard a b childEquiv point all
        subsetPoint subset left right k BConsL(sr_domain_bound_succ M domain k HD)BGuard BA BB'
        HChildEquiv HPoint HAll HSubsetPoint HSubset HLeft HRight PAllL PSubsetL PL).
    - change(source_pcs_sign M domain body a)in HSign.
      change(sr_quantifier M false domain a exD)in HExD.
      assert(E:exD=left)by(eapply sr_quantifier_functional;eassumption). subst exD.
      exact(source_full_tv_exists_forward M lb lc ln domain guard a b childEquiv point all left exA right closure k
        BConsL BGuard BA BB' HChildEquiv HPoint HAll HLeft HExA HRight HClosure PAllL PClosureL PL). }
  pose proof(full_source_II M cb cc cn left right lr lb lc ln(ex_intro _ k(conj BLR BC))PR HConsL HLR)as PLR.
  destruct(environment_cons_total M cb cc cn right)as(rb&rc&rn&HConsR).
  pose proof(proj2(context_bounded_cons M cb cc cn right rb rc rn k HConsR)(conj BR BC))as BConsR.
  pose proof(source_full_cons_head M cb cc cn right rb rc rn k HConsR BR BConsR)as PR'.
  pose proof(source_full_cons_weaken M cb cc cn right rb rc rn k all HConsR BConsR PAll)as PAllR.
  pose proof(source_full_cons_weaken M cb cc cn right rb rc rn k subset HConsR BConsR PSubset)as PSubsetR.
  pose proof(source_full_cons_weaken M cb cc cn right rb rc rn k closure HConsR BConsR PClosure)as PClosureR.
  assert(PL':source_full_prv M rb rc rn left).
  { destruct universal.
    - assert(HNC:source_tv_negative_closure M domain guard a closure).
      { exists negA,exD,exA. unfold piece in HExD,HExA. auto. }
      exact(source_full_tv_all_reverse_from_positive M rb rc rn domain guard a b childEquiv point all closure left right k
        BConsR(sr_domain_bound_succ M domain k HD)BGuard BA BB' HChildEquiv HPoint HAll HNC HLeft HRight PAllR PClosureR PR').
    - exact(source_full_tv_exists_reverse M rb rc rn domain guard a b childEquiv point all subsetPoint subset left exA right k
        BConsR(sr_domain_bound_succ M domain k HD)BGuard BA BB' HChildEquiv HPoint HAll HSubsetPoint HSubset
        HLeft HExA HRight PAllR PSubsetR PR'). }
  pose proof(full_source_II M cb cc cn right left rl rb rc rn(ex_intro _ k(conj BRL BC))PL' HConsR HRL)as PRL.
  exact(full_source_CI M cb cc cn lr rl equiv(ex_intro _ k(conj BE BC))PLR PRL HAnd).
Qed.
Print Assumptions source_full_tv_piece_witness.
Print Assumptions source_tv_quantifier.
