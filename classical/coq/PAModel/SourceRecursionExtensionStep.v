(** Close all three attempt-step variables after the actual value-case proof. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceQuantifierRules
 SourceFiniteTelescope SourceFiniteTelescopeQuantifier SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionAttemptStepShell
 SourceRecursionExtensionPoint SourceRecursionExtensionInputs SourceRecursionExtensionInputShift SourceRecursionBinaryIdentity SourceRecursionFreshPredecessorShell SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Ltac rec_step_bound:=first[assumption|apply coding_zero_lt_succ|apply(proj2(coding_lt_succ_cancel _ _ _));rec_step_bound].
Theorem source_zfr_rec_extension_step M phi o a N f q g z next p w A step law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M q k ->coding_lt M g k ->
 coding_lt M z k ->coding_lt M next k ->coding_lt M p k ->coding_lt M w k ->source_rec_extension_inputs M phi o a N f q g z next p w A ->
 source_rec_attempt_step M phi N g step ->source_finite_telescope M A step law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BQ BG BZ BNext BP' BW HInputs HStep HLaw.
 set(s:=succM M).
 destruct(source_rec_extension_inputs_total M phi(s o)(s a)(s N)(s f)(s q)(s g)(s z)(s next)(s p)(s w))as(A1&HA1).
 destruct(source_rec_extension_inputs_total M phi(s(s o))(s(s a))(s(s N))(s(s f))(s(s q))(s(s g))(s(s z))(s(s next))(s(s p))(s(s w)))as(A2&HA2).
 destruct(source_rec_extension_inputs_total M phi(s(s(s o)))(s(s(s a)))(s(s(s N)))(s(s(s f)))(s(s(s q)))(s(s(s g)))(s(s(s z)))(s(s(s next)))(s(s(s p)))(s(s(s w))))as(A3&HA3).
 pose proof(source_rec_extension_inputs_shift M phi o a N f q g z next p w A A1 BP HInputs HA1)as S1.
 pose proof(source_rec_extension_inputs_shift M phi(s o)(s a)(s N)(s f)(s q)(s g)(s z)(s next)(s p)(s w)A1 A2 BP HA1 HA2)as S2.
 pose proof(source_rec_extension_inputs_shift M phi(s(s o))(s(s a))(s(s N))(s(s f))(s(s q))(s(s g))(s(s z))(s(s next))(s(s p))(s(s w))A2 A3 BP HA2 HA3)as S3.
 pose proof(source_rec_extension_inputs_bounded M phi o a N f q g z next p w A k BP BO BA BN BF BQ BG BZ BNext BP' BW HInputs)as Bounds.
 pose proof(source_finite_shifted_bounds M A A1 k S1 Bounds)as Bounds1.
 pose proof(source_finite_shifted_bounds M A1 A2(s k)S2 Bounds1)as Bounds2.
 destruct(source_rec_attempt_zero_total M o a g)as(first&HFirst).
 destruct(sf_relation_total M SFAnd first step)as(att&HAtt).
 assert(HAttGraph:source_rec_attempt M phi o a N g att)by(exists first,step;auto).
 pose proof(source_rec_attempt_bounded M phi o a N g att k BP BO BA BN BG HAttGraph)as BAtt.
 pose proof(proj2(proj1(source_bounded_accept_binary M SFAnd first step att k(or_introl eq_refl)HAtt)BAtt))as BStep.
 destruct(source_rec_attempt_step_shell M phi N g step HStep)
  as(guard&successor&appOut&appIn&body&ex&t3&t2&point&one&two&HG&HS&HO&HI&HB&HE&H3&H2&HP&HOne&HTwo&HOuter).
 pose proof(proj1(source_bounded_accept_unary M SFAll two step k(or_introl eq_refl)HOuter)BStep)as BTwo.
 pose proof(proj1(source_bounded_accept_unary M SFAll one two(s k)(or_introl eq_refl)HTwo)BTwo)as BOne.
 pose proof(proj1(source_bounded_accept_unary M SFAll point one(s(s k))(or_introl eq_refl)HOne)BOne)as BPoint.
 assert(HTransition:source_rec_transition_witness M phi(s(s(s g)))(code_numeral M 2)(zeroM M)ex).
 { exists appIn,phi,body. split;[exact HI|]. split;[exact(source_rec_binary_identity M phi BP)|]. auto. }
 destruct(source_finite_telescope_total M A3 point)as(pointLaw&HPointLaw).
 assert(PPoint:source_zfr_provable M pointLaw).
 { destruct HA3 as(inj3&att3&mz3&sz3&appf3&adj3&op3&binary3&E3&HInj3&HAtt3&HMZ3&HSZ3&HAF3&HAdj3&HOp3&HBinary3). subst A3.
   assert(HTel:source_finite_telescope M[inj3;att3;mz3;sz3;appf3;adj3;op3;binary3;guard;successor;appOut]ex pointLaw).
   { apply(source_finite_telescope_prefix M[inj3;att3;mz3;sz3;appf3;adj3;op3;binary3][guard;successor;appOut]point ex pointLaw HPointLaw). rec_pack_telescope. }
   apply(source_zfr_rec_extension_point M phi(s(s(s o)))(s(s(s a)))(s(s(s N)))(s(s(s f)))(s(s(s q)))(s(s(s g)))
    (s(s(s z)))(s(s(s next)))(s(s(s p)))(s(s(s w)))(code_numeral M 2)(code_numeral M 1)(zeroM M)
    inj3 att3 mz3 sz3 appf3 adj3 op3 binary3 guard successor appOut ex pointLaw(s(s(s k))));try rec_step_bound;assumption. }
 destruct(source_finite_telescope_total M A2 one)as(oneLaw&HOneLaw).
 pose proof(source_zfr_finite_telescope_all M A2 A3 point one pointLaw oneLaw(s(s k))Bounds2 BPoint S3 HOne HPointLaw HOneLaw PPoint)as POne.
 destruct(source_finite_telescope_total M A1 two)as(twoLaw&HTwoLaw).
 pose proof(source_zfr_finite_telescope_all M A1 A2 one two oneLaw twoLaw(s k)Bounds1 BOne S2 HTwo HOneLaw HTwoLaw POne)as PTwo.
 exact(source_zfr_finite_telescope_all M A A1 two step twoLaw law k Bounds BTwo S1 HOuter HTwoLaw HLaw PTwo).
Qed.
Print Assumptions source_zfr_rec_extension_step.
