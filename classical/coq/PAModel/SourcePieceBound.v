(** One genuine reflection piece has an ordinal witness-closure bound over
    any named set. Both set and ordinal names may be arbitrary model elements. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  SourceBoundMonotone NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalInstantiation SourceRenamingIdentity
  SourceDomainInstances SourceDomainInstanceRenaming SourceRoleReopening SourcePieceClosure SourcePieceClosureFacts SourcePieceRoles
  SourceD0Recipe SourceDn SourceCBGoal SourceCBUniform SourceOrdinalPredicate SourceLFixed SourceHierarchySyntax
  SourceDescriptorClosure SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code source_L_domain_code.

Theorem source_zfr_pc_bound M level count phi g X ordinal pc body ex implication:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_bounded M phi(succM M count) ->
  numerical_instantiation M(source_ordinal_predicate_code M)g ordinal ->
  source_pc_instance M(source_L_domain_code M)level count phi(zeroM M)(succM M X)pc ->
  sf_relation M SFAnd(source_ordinal_predicate_code M)pc body ->sf_relation M SFEx body(zeroM M)ex ->
  sf_relation M SFImpl ordinal ex implication ->source_zfr_provable M implication.
Proof.
  intros HL HB HOrdinal HPC HBody HEx HImp.
  destruct(source_d0_recipe_total M(source_L_domain_code M)level phi) as(d0&HD0).
  destruct(source_dn_total M count d0) as(dn&HDN).
  destruct(sf_relation_total M SFAnd(source_ordinal_predicate_code M)dn) as(oldBody&HOldBody).
  destruct(sf_relation_total M SFEx oldBody(zeroM M)) as(goal&HGoal).
  assert(HCB:source_cb_goal M(source_L_domain_code M)level(source_ordinal_predicate_code M)count phi goal).
  { exists d0,dn,oldBody. auto. }
  destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)(code_numeral M 1)) as(oldOrd&HOldOrd).
  destruct(sf_relation_total M SFImpl oldOrd goal) as(oldImp&HOldImp).
  assert(HB':source_bounded M phi(addM M count(succM M(code_numeral M 1)))).
  { cbn[code_numeral]. rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_zero.
    apply(source_bounded_monotone M phi(succM M count)(succM M(succM M count))HB).
    exact(coding_lt_trans M(succM M count)(succM M(succM M count))(succM M(succM M(succM M count)))
      (coding_lt_succ M(succM M count))(coding_lt_succ M(succM M(succM M count)))). }
  pose proof(source_zfr_cb_uniform M level count phi(code_numeral M 1)oldOrd goal oldImp(code_numeral M 1)
    HL HB'(coding_lt_succ M(code_numeral M 1))HOldOrd HCB HOldImp) as POld.
  destruct(source_role_reopening_total M g X) as(rb&rc&HRole).
  assert(HLookup:forall i,(i<2)%nat ->renaming_lookup M rb rc(code_numeral M 2)(zeroM M)
    (code_numeral M i)(if Nat.eqb i 0 then X else g)).
  { intros i HI. destruct i as[|[|i]];try (exfalso;lia).
    - apply(proj2(renaming_lookup_inside M rb rc(code_numeral M 2)(zeroM M)_ _
        (coding_zero_lt_succ M(code_numeral M 1)))).
      exact(proj1(substitution_lookup_inside M rb rc(code_numeral M 2)(zeroM M)_ _
        (coding_zero_lt_succ M(code_numeral M 1)))(proj1 HRole)).
    - apply(proj2(renaming_lookup_inside M rb rc(code_numeral M 2)(zeroM M)_ _
        (coding_lt_succ M(code_numeral M 1)))).
      exact(proj1(substitution_lookup_inside M rb rc(code_numeral M 2)(zeroM M)_ _
        (coding_lt_succ M(code_numeral M 1)))(proj2 HRole)). }
  destruct(numerical_renaming_total M oldOrd rb rc(code_numeral M 2)(zeroM M)) as(newOrd&HRord).
  pose proof(source_domain_instance_renaming M(source_ordinal_predicate_code M)(code_numeral M 1)oldOrd
    rb rc(code_numeral M 2)(zeroM M)newOrd g(source_ordinal_predicate_bounded M)HOldOrd HRord
    (HLookup 1 ltac:(lia))) as HNewOrd.
  pose proof(numerical_instantiation_functional M(source_ordinal_predicate_code M)g newOrd ordinal HNewOrd HOrdinal) as E.
  subst newOrd.
  destruct(numerical_renaming_total M goal rb rc(code_numeral M 2)(zeroM M)) as(newEx&HRex).
  destruct(proj1(numerical_renaming_quantifier M false oldBody goal rb rc(code_numeral M 2)(zeroM M)newEx HGoal)HRex)
    as(ab&ac&an&newBody&HMap&HRbody&HNewEx).
  destruct(proj1(numerical_renaming_binary M SFAnd(source_ordinal_predicate_code M)dn oldBody
    ab ac an(zeroM M)newBody(or_introl eq_refl)HOldBody)HRbody) as(newO&newPc&HRO&HRpc&HNewBody).
  pose proof(numerical_renaming_lift_fixes_domain M(source_ordinal_predicate_code M)rb rc(code_numeral M 2)(zeroM M)
    ab ac an(source_ordinal_predicate_bounded M)HMap) as HOSelf.
  pose proof(numerical_renaming_functional M(source_ordinal_predicate_code M)ab ac an(zeroM M)
    newO(source_ordinal_predicate_code M)HRO HOSelf) as E. subst newO.
  pose proof(source_LL_instance_bounded M(code_numeral M 1)(zeroM M)level(code_numeral M 2)
    (coding_lt_succ M(code_numeral M 1))(coding_zero_lt_succ M(code_numeral M 1))HL) as HLevelB.
  pose proof(source_pc_dn_bounded M(source_L_domain_code M)level count phi d0 dn
    (numerical_L_domain_bounded M)HLevelB HB HD0 HDN) as HBDN.
  pose proof(source_pc_instance_of_renaming M(source_L_domain_code M)level count phi d0 dn(zeroM M)(succM M X)
    ab ac an(zeroM M)newPc HD0 HDN HBDN HRpc(proj1(proj2 HMap))
    (proj2(proj2 HMap)(zeroM M)X(HLookup 0 ltac:(lia)))) as HNewPC.
  pose proof(source_pc_instance_functional M(source_L_domain_code M)level count phi(zeroM M)(succM M X)
    newPc pc HNewPC HPC) as E. subst newPc.
  pose proof(sf_relation_functional M SFAnd(source_ordinal_predicate_code M)pc newBody body HNewBody HBody) as E. subst newBody.
  pose proof(sf_relation_functional M SFEx body(zeroM M)newEx ex HNewEx HEx) as E. subst newEx.
  assert(HRI:numerical_renaming M oldImp rb rc(code_numeral M 2)(zeroM M)implication).
  { apply(proj2(numerical_renaming_binary M SFImpl oldOrd goal oldImp rb rc(code_numeral M 2)(zeroM M)
      implication(or_intror(or_intror eq_refl))HOldImp)). exists ordinal,ex. auto. }
  apply(proj1(source_zfr_descriptor_provable M implication)).
  exact(source_descriptor_provable_renaming M ZFRSourceDescriptor oldImp rb rc(code_numeral M 2)(zeroM M)
    implication(proj2(source_zfr_descriptor_provable M oldImp)POld)HRI).
Qed.

Print Assumptions source_zfr_pc_bound.
