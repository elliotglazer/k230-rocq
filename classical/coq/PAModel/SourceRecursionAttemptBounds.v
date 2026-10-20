(** Genuine source bounds for attempts with a binary internal matrix. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptStepShell SourceFiniteCutoffShift.
Unset Implicit Arguments.
Theorem source_rec_attempt_bounded M phi o a N f out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->
 source_rec_attempt M phi o a N f out ->source_bounded M out k.
Proof.
 intros BP BO BA BN BF(first&second&HFirst&HSecond&HOut).
 destruct HFirst as(app&eq&point&HApp&HEq&HPoint&HAll).
 pose proof(source_rec_app_bounded M(succM M f)(succM M o)(zeroM M)app(succM M k)
  (proj2(coding_lt_succ_cancel M f k)BF)(proj2(coding_lt_succ_cancel M o k)BO)(coding_zero_lt_succ M k)HApp)as BApp.
 pose proof(proj2(source_bounded_accept_atom M SFEqual _ _ eq(succM M k)(or_intror eq_refl)HEq)
  (conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M a k)BA)))as BEq.
 pose proof(proj2(source_bounded_accept_binary M SFImpl app eq point(succM M k)(or_intror(or_intror eq_refl))HPoint)(conj BApp BEq))as BPoint.
 pose proof(proj2(source_bounded_accept_unary M SFAll point first k(or_introl eq_refl)HAll)BPoint)as BFirst.
 destruct(source_rec_attempt_step_shell M phi N f second HSecond)
  as(guard&successor&appOut&appIn&body&ex&t3&t2&point'&one&two&HG&HS&HO&HI&HBody&HEx&H3&H2&HPoint'&HOne&HTwo&HOuter).
 assert(F3:coding_lt M(source_succ_iter M 3 f)(source_succ_iter M 3 k)).
 { change(coding_lt M(succM M(succM M(succM M f)))(succM M(succM M(succM M k)))).
   apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_lt_succ_cancel. exact BF. }
 assert(N3:coding_lt M(source_succ_iter M 3 N)(source_succ_iter M 3 k)).
 { change(coding_lt M(succM M(succM M(succM M N)))(succM M(succM M(succM M k)))).
   apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_lt_succ_cancel. exact BN. }
 assert(I0:coding_lt M(zeroM M)(source_succ_iter M 3 k))by apply coding_zero_lt_succ.
 assert(I1:coding_lt M(code_numeral M 1)(source_succ_iter M 3 k)).
 { apply coding_lt_succ_cancel,coding_zero_lt_succ. }
 assert(I2:coding_lt M(code_numeral M 2)(source_succ_iter M 3 k)).
 { apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ. }
 pose proof(proj2(source_bounded_accept_atom M SFMember _ _ guard(source_succ_iter M 3 k)(or_introl eq_refl)HG)(conj I2 N3))as BG.
 pose proof(source_rec_successor_bounded M _ _ successor(source_succ_iter M 3 k)I2 I1 HS)as BS.
 pose proof(source_rec_app_bounded M _ _ _ appOut(source_succ_iter M 3 k)F3 I1 I0 HO)as BO'.
 pose proof(source_rec_app_bounded M _ _ _ appIn(source_succ_iter M 4 k)
  (proj2(coding_lt_succ_cancel M _ _)F3)(proj2(coding_lt_succ_cancel M _ _)I2)(coding_zero_lt_succ M(source_succ_iter M 3 k))HI)as BI.
 assert(BP4:source_bounded M phi(source_succ_iter M 4 k)).
 { apply(source_bounded_monotone M phi(code_numeral M 2)(source_succ_iter M 4 k)BP).
   apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ. }
 pose proof(proj2(source_bounded_accept_binary M SFAnd appIn phi body(source_succ_iter M 4 k)(or_introl eq_refl)HBody)(conj BI BP4))as BBody.
 pose proof(proj2(source_bounded_accept_unary M SFEx body ex(source_succ_iter M 3 k)(or_intror eq_refl)HEx)BBody)as BEx.
 pose proof(proj2(source_bounded_accept_binary M SFImpl appOut ex t3(source_succ_iter M 3 k)(or_intror(or_intror eq_refl))H3)(conj BO' BEx))as B3.
 pose proof(proj2(source_bounded_accept_binary M SFImpl successor t3 t2(source_succ_iter M 3 k)(or_intror(or_intror eq_refl))H2)(conj BS B3))as B2.
 pose proof(proj2(source_bounded_accept_binary M SFImpl guard t2 point'(source_succ_iter M 3 k)(or_intror(or_intror eq_refl))HPoint')(conj BG B2))as BPoint'.
 pose proof(proj2(source_bounded_accept_unary M SFAll point' one(source_succ_iter M 2 k)(or_introl eq_refl)HOne)BPoint')as BOne.
 pose proof(proj2(source_bounded_accept_unary M SFAll one two(succM M k)(or_introl eq_refl)HTwo)BOne)as BTwo.
 pose proof(proj2(source_bounded_accept_unary M SFAll two second k(or_introl eq_refl)HOuter)BTwo)as BSecond.
 exact(proj2(source_bounded_accept_binary M SFAnd first second out k(or_introl eq_refl)HOut)(conj BFirst BSecond)).
Qed.
Print Assumptions source_rec_attempt_bounded.
