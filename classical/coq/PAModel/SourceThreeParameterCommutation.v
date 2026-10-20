(** Arbitrary-model renaming of fixed three-role source formulas. It is
    an arithmetic commuting square between genuine finite prefix maps. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourceBounded FixedSourceBounds SourceNumeralLift SourceFiniteParameters SourceFiniteParameterProofs
 ThreeNameRenaming NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity SourceRenamingDiamond.
From Undecidability.FOL Require Import Syntax.Bounded.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Lemma source_three_parameter_syntax_renaming M(phi:sf_form)rho b c f :
 renaming_lookup M b c(code_numeral M 3)(zeroM M)(code_numeral M 0)(rho 0) ->
 renaming_lookup M b c(code_numeral M 3)(zeroM M)(code_numeral M 1)(rho 1) ->
 renaming_lookup M b c(code_numeral M 3)(zeroM M)(code_numeral M 2)(rho 2) ->
 code_relation M rho(source_parameter_expression source_three_parameter_names phi) f ->
 numerical_renaming M(code_numeral M(sf_encode phi))b c(code_numeral M 3)(zeroM M)f.
Proof.
 intros H0 H1 H2 HF. apply(source_finite_parameter_renaming M phi source_three_parameter_names rho
   b c(code_numeral M 3)(zeroM M)f);[|exact HF].
 intros[|[|[|i]]] x HX;cbn[source_three_parameter_names]in HX.
 - change(x=rho 0)in HX. now subst x.
 - change(x=rho 1)in HX. now subst x.
 - change(x=rho 2)in HX. now subst x.
 - change(x=code_numeral M(S(S(S i))))in HX. subst x.
   apply(proj2(renaming_lookup_outside M b c(code_numeral M 3)(zeroM M)
    (code_numeral M(S(S(S i))))(code_numeral M(S(S(S i))))
    ltac:(intro HBad;apply(proj1(fixed_source_numeral_lt_iff M(S(S(S i)))3))in HBad;lia))).
   symmetry. apply coding_add_zero_r.
Qed.
Theorem source_three_parameter_renaming_commutation M(phi:sf_form)rho other f g b c n delta :
 bounded 3 phi ->
 code_relation M rho(source_parameter_expression source_three_parameter_names phi) f ->
 code_relation M other(source_parameter_expression source_three_parameter_names phi) g ->
 (forall i,(i<3)%nat ->renaming_lookup M b c n delta(rho i)(other i)) ->
 numerical_renaming M f b c n delta g.
Proof.
 intros HB HF HG HNames.
 destruct(three_name_renaming_total M(rho 0)(rho 1)(rho 2)(zeroM M))as(ob&oc&H0&H1&H2).
 destruct(three_name_renaming_total M(other 0)(other 1)(other 2)(zeroM M))as(nb&nc&J0&J1&J2).
 pose proof(source_three_parameter_syntax_renaming M phi rho ob oc f H0 H1 H2 HF)as HOld.
 pose proof(source_three_parameter_syntax_renaming M phi other nb nc g J0 J1 J2 HG)as HNew.
 assert(BPhi:source_bounded M(code_numeral M(sf_encode phi))(code_numeral M 3)).
 { exact(proj2(fixed_source_bounded_iff phi M(fun _=>zeroM M)(code_numeral M(sf_encode phi))3
    (source_formula_numeral_graph M phi)) HB). }
 assert(HI:numerical_renaming M(code_numeral M(sf_encode phi))(zeroM M)(zeroM M)(zeroM M)(zeroM M)
   (code_numeral M(sf_encode phi))).
 { apply(numerical_renaming_identity_on_bound M _ _ _ _ _(code_numeral M 3) BPhi).
   intros i _. right. split;[apply coding_not_lt_zero|symmetry;apply coding_add_zero_r]. }
 apply(numerical_source_renaming_diamond M(code_numeral M(sf_encode phi))(code_numeral M 3)
   (zeroM M)(zeroM M)(zeroM M)(zeroM M) ob oc(code_numeral M 3)(zeroM M)
   nb nc(code_numeral M 3)(zeroM M) b c n delta
   (code_numeral M(sf_encode phi)) f g BPhi HI HOld HNew).
 intros i j l m HI' HJ HM HL.
 assert(EJ:j=i).
 { apply(renaming_lookup_outside M(zeroM M)(zeroM M)(zeroM M)(zeroM M)i j(coding_not_lt_zero M i))in HJ.
   now rewrite coding_add_zero_r in HJ. }
 subst j. destruct(source_numeral_initial_segment M 3 i HI')as(index&HIndex&->).
 destruct index as[|[|[|index]]];try lia.
 - assert(EL:l=rho 0)by(eapply renaming_lookup_functional;[exact HL|exact H0]).
   assert(EM:m=other 0)by(eapply renaming_lookup_functional;[exact HM|exact J0]).
   subst l m. apply HNames. lia.
 - assert(EL:l=rho 1)by(eapply renaming_lookup_functional;[exact HL|exact H1]).
   assert(EM:m=other 1)by(eapply renaming_lookup_functional;[exact HM|exact J1]).
   subst l m. apply HNames. lia.
 - assert(EL:l=rho 2)by(eapply renaming_lookup_functional;[exact HL|exact H2]).
   assert(EM:m=other 2)by(eapply renaming_lookup_functional;[exact HM|exact J2]).
   subst l m. apply HNames. lia.
Qed.
Print Assumptions source_three_parameter_renaming_commutation.
