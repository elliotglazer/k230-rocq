(** Actual substitution through the varying-matrix attempt predicate. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 SourceFiniteCutoffShift NumericalSubstitutionMaps NumericalSubstitution SourceSubstitutionIdentity
 SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport SourceRecursionAttempt SourceRecursionAttemptStepShell.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Ltac attempt_substitution :=first[assumption|
 lazymatch goal with
 | |-numerical_substitution ?M ?f ?b ?c ?n ?base ?g=>
  match goal with
  | HF:sf_relation M SFImpl ?a ?d f,HG:sf_relation M SFImpl ?a' ?d' g|-_=>
    apply(proj2(numerical_substitution_binary M SFImpl a d f b c n base g(or_intror(or_intror eq_refl))HF));
    exists a',d';split;[attempt_substitution|split;[attempt_substitution|exact HG]]
  | HF:sf_relation M SFAnd ?a ?d f,HG:sf_relation M SFAnd ?a' ?d' g|-_=>
    apply(proj2(numerical_substitution_binary M SFAnd a d f b c n base g(or_introl eq_refl)HF));
    exists a',d';split;[attempt_substitution|split;[attempt_substitution|exact HG]]
  end
 end].
Theorem source_rec_attempt_step_substitution M phi N f old N' f' new rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_attempt_step M phi N f old ->source_rec_attempt_step M phi N' f' new ->
 substitution_lookup M rb rc rn base N N' ->substitution_lookup M rb rc rn base f f' ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros BP HO HN HMapN HMapF.
 destruct(source_rec_attempt_step_shell M phi N f old HO)as(guard&successor&appOut&appIn&body&ex&t3&t2&point&one&two&
  HG&HS&HAO&HAI&HB&HE&H3&H2&HP&H1&H2A&HF).
 destruct(source_rec_attempt_step_shell M phi N' f' new HN)as(guard'&successor'&appOut'&appIn'&body'&ex'&t3'&t2'&point'&one'&two'&
  HG'&HS'&HAO'&HAI'&HB'&HE'&H3'&H2'&HP'&H1'&H2A'&HF').
 destruct(substitution_lift_total M rb rc rn base)as(b1&c1&n1&L1).
 destruct(substitution_lift_total M b1 c1 n1(succM M base))as(b2&c2&n2&L2).
 destruct(substitution_lift_total M b2 c2 n2(succM M(succM M base)))as(b3&c3&n3&L3).
 destruct(substitution_lift_total M b3 c3 n3(succM M(succM M(succM M base))))as(b4&c4&n4&L4).
 set(base3:=succM M(succM M(succM M base))). set(base4:=succM M base3).
 assert(F0:substitution_lookup M b3 c3 n3 base3(zeroM M)(zeroM M))by exact(proj1(proj2 L3)).
 assert(F1:substitution_lookup M b3 c3 n3 base3(code_numeral M 1)(code_numeral M 1)).
 { exact(proj2(proj2 L3)(zeroM M)(zeroM M)(proj1(proj2 L2))). }
 assert(F2:substitution_lookup M b3 c3 n3 base3(code_numeral M 2)(code_numeral M 2)).
 { exact(proj2(proj2 L3)(code_numeral M 1)(code_numeral M 1)
    (proj2(proj2 L2)(zeroM M)(zeroM M)(proj1(proj2 L1)))). }
 assert(N3:substitution_lookup M b3 c3 n3 base3(source_succ_iter M 3 N)(source_succ_iter M 3 N')).
 { exact(proj2(proj2 L3)_ _(proj2(proj2 L2)_ _(proj2(proj2 L1)_ _ HMapN))). }
 assert(SF3:substitution_lookup M b3 c3 n3 base3(source_succ_iter M 3 f)(source_succ_iter M 3 f')).
 { exact(proj2(proj2 L3)_ _(proj2(proj2 L2)_ _(proj2(proj2 L1)_ _ HMapF))). }
 assert(Z4:substitution_lookup M b4 c4 n4 base4(zeroM M)(zeroM M))by exact(proj1(proj2 L4)).
 assert(O4:substitution_lookup M b4 c4 n4 base4(code_numeral M 1)(code_numeral M 1))by exact(proj2(proj2 L4)_ _ F0).
 assert(T4:substitution_lookup M b4 c4 n4 base4(code_numeral M 3)(code_numeral M 3))by exact(proj2(proj2 L4)_ _ F2).
 assert(SF4:substitution_lookup M b4 c4 n4 base4(source_succ_iter M 4 f)(source_succ_iter M 4 f'))by exact(proj2(proj2 L4)_ _ SF3).
 assert(SGuard:numerical_substitution M guard b3 c3 n3 base3 guard').
 { apply(proj2(numerical_substitution_member M _ _ _ b3 c3 n3 base3 guard' HG)). exists(code_numeral M 2),(source_succ_iter M 3 N'). auto. }
 pose proof(source_rec_successor_substitution M _ _ successor _ _ successor' b3 c3 n3 base3 HS HS' F2 F1)as SSuccessor.
 pose proof(source_rec_app_substitution M _ _ _ appOut _ _ _ appOut' b3 c3 n3 base3 HAO HAO' SF3 F1 F0)as SAppOut.
 pose proof(source_rec_app_substitution M _ _ _ appIn _ _ _ appIn' b4 c4 n4 base4 HAI HAI' SF4 T4 Z4)as SAppIn.
 assert(SPhi:numerical_substitution M phi b4 c4 n4 base4 phi).
 { apply(numerical_substitution_identity_on_bound M phi b4 c4 n4 base4(code_numeral M 2)BP).
   intros i HI. destruct(source_numeral_initial_segment M 2 i HI)as(idx&HNidx&->).
   destruct idx as[|[|idx]];[exact Z4|exact O4|lia]. }
 assert(SEx:numerical_substitution M ex b3 c3 n3 base3 ex').
 { apply(proj2(numerical_substitution_quantifier M false body ex b3 c3 n3 base3 ex' HE)).
   exists b4,c4,n4,body'. split;[exact L4|]. split;[attempt_substitution|exact HE']. }
 assert(SPoint:numerical_substitution M point b3 c3 n3 base3 point')by attempt_substitution.
 apply(proj2(numerical_substitution_quantifier M true two old rb rc rn base new HF)).
 exists b1,c1,n1,two'. split;[exact L1|]. split;[|exact HF'].
 apply(proj2(numerical_substitution_quantifier M true one two b1 c1 n1(succM M base)two' H2A)).
 exists b2,c2,n2,one'. split;[exact L2|]. split;[|exact H2A'].
 apply(proj2(numerical_substitution_quantifier M true point one b2 c2 n2(succM M(succM M base))one' H1)).
 exists b3,c3,n3,point'. auto.
Qed.
Print Assumptions source_rec_attempt_step_substitution.
Theorem source_rec_attempt_zero_substitution M o a f old o' a' f' new rb rc rn base:
 source_rec_attempt_zero M o a f old ->source_rec_attempt_zero M o' a' f' new ->
 substitution_lookup M rb rc rn base o o' ->substitution_lookup M rb rc rn base a a' ->
 substitution_lookup M rb rc rn base f f' ->numerical_substitution M old rb rc rn base new.
Proof.
 intros(app&equal&point&HA&HE&HP&HO)(app'&equal'&point'&HA'&HE'&HP'&HO')HMapO HMapA HMapF.
 destruct(substitution_lift_total M rb rc rn base)as(b&c&n&HL).
 pose proof(proj1(proj2 HL))as HZero.
 pose proof(proj2(proj2 HL)_ _ HMapO)as HSO.
 pose proof(proj2(proj2 HL)_ _ HMapA)as HSA.
 pose proof(proj2(proj2 HL)_ _ HMapF)as HSF.
 pose proof(source_rec_app_substitution M _ _ _ app _ _ _ app' b c n(succM M base)HA HA' HSF HSO HZero)as SApp.
 assert(SEqual:numerical_substitution M equal b c n(succM M base)equal').
 { apply(proj2(numerical_substitution_equal M _ _ _ b c n(succM M base)equal' HE)).
   exists(zeroM M),(succM M a'). auto. }
 apply(proj2(numerical_substitution_quantifier M true point old rb rc rn base new HO)).
 exists b,c,n,point'. split;[exact HL|]. split;[attempt_substitution|exact HO'].
Qed.
Theorem source_rec_attempt_substitution M phi o a N f old o' a' N' f' new rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_attempt M phi o a N f old ->source_rec_attempt M phi o' a' N' f' new ->
 substitution_lookup M rb rc rn base o o' ->substitution_lookup M rb rc rn base a a' ->
 substitution_lookup M rb rc rn base N N' ->substitution_lookup M rb rc rn base f f' ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros BP(first&second&HF&HS&HO)(first'&second'&HF'&HS'&HO')HMapO HMapA HMapN HMapF.
 pose proof(source_rec_attempt_zero_substitution M o a f first o' a' f' first' rb rc rn base HF HF' HMapO HMapA HMapF)as SFirst.
 pose proof(source_rec_attempt_step_substitution M phi N f second N' f' second' rb rc rn base BP HS HS' HMapN HMapF)as SSecond.
 attempt_substitution.
Qed.
Print Assumptions source_rec_attempt_zero_substitution.
Print Assumptions source_rec_attempt_substitution.
