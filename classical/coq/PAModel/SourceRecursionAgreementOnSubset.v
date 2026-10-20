(** Actual universal agreement from the subset chart and N subset X. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 NumericalRenaming SourceQuantifierRules SourceFiniteTelescope SourceFiniteTelescopeQuantifier SourceZFRFiniteRule SourceRawSubset SourceRecursionPrimitiveRelations
 SourceRecursionAgreementSubset SourceRecursionAgreementOn SourceRecursionSubsetBounds SourceRecursionSubsetRules SourceRecursionInductionTransport SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Lemma source_rec_raw_subset_bounded M N X out k:coding_lt M N k ->coding_lt M X k ->source_raw_subset_graph M N X out ->source_bounded M out k.
Proof.
 intros BN BX(mn&mx&point&HN&HX&HP&HO).
 assert(BMN:source_bounded M mn(succM M k))by exact(proj2(source_bounded_accept_atom M SFMember _ _ mn(succM M k)(or_introl eq_refl)HN)
  (conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M N k)BN))).
 assert(BMX:source_bounded M mx(succM M k))by exact(proj2(source_bounded_accept_atom M SFMember _ _ mx(succM M k)(or_introl eq_refl)HX)
  (conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M X k)BX))).
 exact(proj2(source_bounded_accept_unary M SFAll point out k(or_introl eq_refl)HO)
  (proj2(source_bounded_accept_binary M SFImpl mn mx point(succM M k)(or_intror(or_intror eq_refl))HP)(conj BMN BMX))).
Qed.
Theorem source_zfr_rec_agreement_on_subset M f g N X chart subset target law k:
 coding_lt M f k ->coding_lt M g k ->coding_lt M N k ->coding_lt M X k ->source_rec_subset_chart M f g N X chart ->
 source_raw_subset_graph M N X subset ->source_rec_agrees_on M f g N target ->source_finite_telescope M[chart;subset]target law ->source_zfr_provable M law.
Proof.
 intros BF BG BN BX HChart HSubset HTarget HLaw.
 destruct(source_rec_subset_chart_total M(succM M f)(succM M g)(succM M N)(succM M X))as(chart1&HChart1).
 destruct(source_raw_subset_total M(succM M N)(succM M X))as(subset1&HSubset1).
 pose proof(source_rec_subset_chart_shift M f g N X chart chart1 HChart HChart1)as SChart.
 destruct(numerical_renaming_total M subset(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(s'&SS').
 pose proof(source_raw_subset_shift M N X subset s' HSubset SS')as HSubset'.
 destruct HSubset' as(a&b&p&HA&HB&HP&HO). destruct HSubset1 as(a1&b1&p1&HA1&HB1&HP1&HO1).
 pose proof(sf_relation_functional M SFMember _ _ a a1 HA HA1)as E. subst a1.
 pose proof(sf_relation_functional M SFMember _ _ b b1 HB HB1)as E. subst b1.
 pose proof(sf_relation_functional M SFImpl a b p p1 HP HP1)as E. subst p1.
 pose proof(sf_relation_functional M SFAll p(zeroM M)s' subset1 HO HO1)as E. subst s'.
 assert(HSubset1:source_raw_subset_graph M(succM M N)(succM M X)subset1)by(exists a,b,p;auto).
 pose proof(source_rec_agrees_on_bounded M f g N target k BF BG BN HTarget)as BTarget.
 destruct HTarget as(member&agr&point&HM&HAgr&HPoint&HAll).
 pose proof(proj1(source_bounded_accept_unary M SFAll point target k(or_introl eq_refl)HAll)BTarget)as BPoint.
 destruct(source_finite_telescope_total M[chart1;subset1]point)as(pointLaw&HPointLaw).
 assert(PStep:source_zfr_provable M pointLaw).
 { apply(source_zfr_finite_rule M[][chart1;subset1;member]agr pointLaw(succM M k)).
   - intros x[<-|[<-|[<-|[]]]].
     + exact(source_rec_subset_chart_bounded M _ _ _ _ chart1(succM M k)(proj2(coding_lt_succ_cancel M f k)BF)(proj2(coding_lt_succ_cancel M g k)BG)(proj2(coding_lt_succ_cancel M N k)BN)(proj2(coding_lt_succ_cancel M X k)BX)HChart1).
     + exact(source_rec_raw_subset_bounded M _ _ subset1(succM M k)(proj2(coding_lt_succ_cancel M N k)BN)(proj2(coding_lt_succ_cancel M X k)BX)HSubset1).
     + exact(proj1(proj1(source_bounded_accept_binary M SFImpl member agr point(succM M k)(or_intror(or_intror eq_refl))HPoint)BPoint)).
   - exact(proj2(proj1(source_bounded_accept_binary M SFImpl member agr point(succM M k)(or_intror(or_intror eq_refl))HPoint)BPoint)).
   - apply(source_finite_telescope_prefix M[chart1;subset1][member]point agr pointLaw HPointLaw). exists agr. split;[reflexivity|exact HPoint].
   - intros x HX. contradiction.
   - intros cb cc cn BC Laws Premises.
     assert(PChart:source_full_prv M cb cc cn chart1)by(apply Premises;cbn;tauto).
     assert(PSubset:source_full_prv M cb cc cn subset1)by(apply Premises;cbn;tauto).
     assert(PMember:source_full_prv M cb cc cn member)by(apply Premises;cbn;tauto).
     destruct(sf_relation_total M SFMember(zeroM M)(succM M X))as(mx&HMX).
     pose proof(source_full_raw_subset_member M cb cc cn(succM M N)(succM M X)(zeroM M)subset1 member mx HSubset1 HM HMX PSubset PMember)as PMX.
     exact(proj2(source_full_rec_subset_chart_out M cb cc cn(succM M f)(succM M g)(succM M N)(succM M X)(zeroM M)chart1 mx member agr HChart1 HMX HM HAgr PChart PMX)). }
 apply(source_zfr_finite_telescope_all M[chart;subset][chart1;subset1]point target pointLaw law k).
 - intros x[<-|[<-|[]]].
   + exact(source_rec_subset_chart_bounded M f g N X chart k BF BG BN BX HChart).
   + exact(source_rec_raw_subset_bounded M N X subset k BN BX HSubset).
 - exact BPoint.
 - repeat(constructor;[assumption|]). constructor.
 - exact HAll.
 - exact HPointLaw.
 - exact HLaw.
 - exact PStep.
Qed.
Print Assumptions source_rec_raw_subset_bounded.
Print Assumptions source_zfr_rec_agreement_on_subset.
