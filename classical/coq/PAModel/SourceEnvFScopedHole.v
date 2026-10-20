(** Arithmetic normalization of an EnvF hole beneath the three finite
 An successor binders. Only its witness0 is captured; all parameter names
 are shifted three times. The internal formula is never decoded. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity SourceRenamingDiamond SourceShiftSpecialization
 SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceNamedCutoffQuantifiers SourceRepresentativeRenaming
 SourceNamedScopes SourceNamedScopeBinding.
From FOL.Tennenbaum Require Peano.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition source_low_parameter_shift M depth f g:=
 numerical_renaming M f(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M depth)g.
Lemma low_parameter_lookup_zero M depth:
 renaming_lookup M(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M depth)(zeroM M)(zeroM M).
Proof. left. split;[apply coding_zero_lt_succ|apply beta_singleton]. Qed.
Lemma low_parameter_lookup_nonzero M depth i:i<>zeroM M ->
 renaming_lookup M(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M depth)i(addM M i(code_numeral M depth)).
Proof.
 intro HN. right. split;[|reflexivity]. intro H.
 apply(proj1(coding_lt_succ_cases M i(zeroM M)))in H.
 destruct H as[H|H];[exact(coding_not_lt_zero M i H)|contradiction].
Qed.
Theorem source_low_parameter_shift_zero M f k:source_bounded M f k ->source_low_parameter_shift M 0 f f.
Proof.
 intro BF. apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF).
 intros i _. destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[j ->]].
 - apply low_parameter_lookup_zero.
 - rewrite<-(coding_add_zero_r M(succM M j))at 2. apply low_parameter_lookup_nonzero.
   intro E. exact(Model.zero_ne_succ M j(eq_sym E)).
Qed.
Theorem source_low_parameter_shift_step M depth f previous result k:
 source_bounded M f k ->source_low_parameter_shift M depth f previous ->
 source_cutoff_shift M 1 previous result ->source_low_parameter_shift M(S depth)f result.
Proof.
 intros BF HR(b&c&n&HM&HS).
 pose proof(source_cutoff_shift_map_renaming M 1 previous result b c n HM HS)as HT.
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF). intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f k
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M depth)
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  b c n(code_numeral M 1)
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M(S depth))previous f result BF HR HId HT).
 intros i j l m HI HJ HM0 HIdI.
 rewrite(renaming_lookup_functional M _ _ _ _ i l i HIdI(source_empty_renaming_lookup M i)).
 apply(source_cutoff_one_raw_zero M b c n HM)in HM0.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(low_parameter_lookup_zero M depth))in HM0.
   destruct HM0 as[[_ ->]|[HN _]];[apply low_parameter_lookup_zero|contradiction].
 - assert(HNon:succM M q<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M q(eq_sym E))).
   rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(low_parameter_lookup_nonzero M depth(succM M q)HNon))in HM0.
   rewrite Arithmetic.add_succ in HM0.
   destruct HM0 as[[E _]|[_ ->]];[exfalso;exact(Model.zero_ne_succ M(addM M q(code_numeral M depth))(eq_sym E))|].
   replace(succM M(succM M(addM M q(code_numeral M depth))))with(addM M(succM M q)(code_numeral M(S depth))).
   + apply low_parameter_lookup_nonzero. exact HNon.
   + change(addM M(succM M q)(succM M(code_numeral M depth))=succM M(succM M(addM M q(code_numeral M depth)))).
     rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_comm,Arithmetic.add_succ. reflexivity.
Qed.
Theorem source_representative_three_scopes M f renamed deep p e a k:
 source_bounded M f k ->~coding_lt M p k ->~coding_lt M e k ->~coding_lt M a k ->
 source_representative_renaming M p f renamed ->source_low_parameter_shift M 3 f deep ->
 named_scope_renaming M[p;e;a]renamed deep.
Proof.
 intros BF HP HE HA HR HDeep.
 destruct(named_scope_map_total M[p;e;a])as(b&c&HMap). exists b,c. split;[exact HMap|].
 assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
 { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k BF). intros i _. apply source_empty_renaming_lookup. }
 apply(numerical_source_renaming_diamond M f k
  (zeroM M)(zeroM M)(zeroM M)(zeroM M) p p(code_numeral M 1)(zeroM M)
  (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 3)
  b c(named_scope_bound M[p;e;a])(code_numeral M 3)f renamed deep BF HId HR HDeep).
 intros i j l m HI HJ HM HName.
 rewrite(renaming_lookup_functional M _ _ _ _ i j i HJ(source_empty_renaming_lookup M i))in HM.
 apply HMap.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - rewrite(renaming_lookup_functional M _ _ _ _ _ l p HName(representative_lookup_zero M p)).
   rewrite(renaming_lookup_functional M _ _ _ _ _ m _ HM(low_parameter_lookup_zero M 3)). left. auto.
 - assert(HNon:succM M q<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M q(eq_sym E))).
   rewrite(renaming_lookup_functional M _ _ _ _ _ l _ HName(representative_lookup_nonzero M p(succM M q)HNon)).
   rewrite(renaming_lookup_functional M _ _ _ _ _ m _ HM(low_parameter_lookup_nonzero M 3(succM M q)HNon)).
   destruct(named_scope_index_total M[p;e;a](succM M q))as(v&HV).
   assert(HNames:forall name,In name[p;e;a] ->succM M q<>name).
   { intros name[<-|[<-|[<-|[]]]]E;subst;contradiction. }
   pose proof(named_scope_index_default M[p;e;a](succM M q)v HNames HV)as EV.
   rewrite named_scope_succ_add in EV. cbn[length]in EV. now rewrite<-EV.
Qed.
Print Assumptions source_low_parameter_shift_step.
Print Assumptions source_representative_three_scopes.
