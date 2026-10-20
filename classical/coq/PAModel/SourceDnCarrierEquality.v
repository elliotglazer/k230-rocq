(** Unconditional actual ZFR carrier-equality transport for a genuine Dn
    piece. Both its payload and parameter count may be nonstandard. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  SourceFiniteCutoffShift SourceD0Recipe SourceD0CarrierBase SourceHierarchySyntax SourceDn SourceDnCarrierMap
  SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_zfr_dn_carrier_equality M domain level phi count d0 dn before after condition map law :
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_bounded M phi(succM M count) ->source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_d0_recipe M domain level phi d0 ->source_dn M count d0 dn ->
  source_cutoff_shift M 2 dn before ->source_cutoff_shift M 1 dn after ->
  sf_relation M SFEqual(code_numeral M 1)(code_numeral M 2)condition ->
  sf_relation M SFImpl before after map ->sf_relation M SFImpl condition map law ->source_zfr_provable M law.
Proof.
  intros HD HL HP HLevel HD0 HDN HBefore HAfter HCondition HMap HLaw.
  destruct(source_cutoff_shift_total M 2 d0)as(pa&HPA).
  destruct(source_cutoff_shift_total M 1 d0)as(pb&HPB).
  destruct(sf_relation_total M SFImpl pa pb)as(baseMap&HBaseMap).
  destruct(sf_relation_total M SFImpl condition baseMap)as(base&HBase).
  pose proof(source_zfr_d0_carrier_base M domain level phi d0 pa pb condition baseMap base count
    HD HL HP HLevel HD0 HPA HPB HCondition HBaseMap HBase)as PBase.
  assert(HBodyBound:source_bounded M d0(addM M count(succM M(succM M(zeroM M))))).
  { rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_zero.
    exact(source_d0_recipe_bounded M domain level phi d0 count HD HL HP HD0). }
  exact(source_zfr_dn_carrier_map M count condition d0 pa pb dn before after(zeroM M)
    baseMap base map law HCondition HBodyBound HDN HPA HPB HBefore HAfter HBaseMap HBase HMap HLaw PBase).
Qed.
Print Assumptions source_zfr_dn_carrier_equality.
