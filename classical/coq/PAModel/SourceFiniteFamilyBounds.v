(** Common arithmetic bounds for externally finite proof frames. Neither
    formula codes nor the source-variable names are assumed standard. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes
 SourceBounded SourceBoundMonotone NumericalRenaming SourceNamedVacuity RawBinderRenaming
 SourceQuantifierRules NumericalContextRenaming SourceRenamingBounds SourceRenamingWellformedness.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_finite_names_bound M(names:list(carrier M)):
 exists k,forall x,In x names ->coding_lt M x k.
Proof.
 induction names as[|x names[k IH]];[exists(zeroM M);intros y H;contradiction|].
 exists(succM M(addM M x k)). intros y[<-|HY].
 - apply coding_le_add.
 - eapply coding_lt_trans;[exact(IH y HY)|]. rewrite Arithmetic.add_comm. apply coding_le_add.
Qed.
Theorem source_finite_formulas_bound M(forms:list(carrier M)):
 (forall f,In f forms ->exists k,source_bounded M f k) ->
 exists k,forall f,In f forms ->source_bounded M f k.
Proof.
 induction forms as[|f forms IH];intro H;[exists(zeroM M);intros g HG;contradiction|].
 destruct(H f(or_introl eq_refl))as(k&HF).
 destruct(IH ltac:(intros g HG;exact(H g(or_intror HG))))as(l&HL).
 exists(addM M k l). intros g[<-|HG].
 - exact(source_bounded_monotone M f k _ HF(coding_le_add M k l)).
 - apply(source_bounded_monotone M g l _ (HL g HG)). rewrite Arithmetic.add_comm. apply coding_le_add.
Qed.
Theorem source_member_bounded_exists M a b member:
 sf_relation M SFMember a b member ->exists k,source_bounded M member k.
Proof.
 intro HM. exists(succM M(addM M a b)).
 apply(proj2(source_bounded_accept_atom M SFMember a b member _(or_introl eq_refl)HM)).
 split;[apply coding_le_add|rewrite Arithmetic.add_comm;apply coding_le_add].
Qed.
Theorem source_renamed_bounded_exists M f g b c n delta k:
 source_bounded M f k ->numerical_renaming M f b c n delta g ->exists l,source_bounded M g l.
Proof.
 intros HF HG. destruct(source_renaming_range_bound M b c n delta k)as(l&HL).
 exists l. exact(numerical_renaming_preserves_bound M f b c n delta g k l HF HG HL).
Qed.
Theorem source_named_member_vacuous M a b member x:
 a<>x ->b<>x ->sf_relation M SFMember a b member ->source_named_vacuous M x member.
Proof.
 intros HAX HBX HM rb rc closed shifted HMap HC HS.
 destruct(proj1(numerical_renaming_member M a b member rb rc(succM M x)(code_numeral M 1)closed HM)HC)
 as(ar&br&HAR&HBR&HClosed).
 destruct(proj1(numerical_renaming_member M a b member(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)shifted HM)HS)
 as(as'&bs'&HAS&HBS&HShift).
 apply(proj1(HMap a ar))in HAR. destruct HAR as[[E _]|[_ ->]];[contradiction|].
 apply(proj1(HMap b br))in HBR. destruct HBR as[[E _]|[_ ->]];[contradiction|].
 apply context_shift_lookup in HAS. apply context_shift_lookup in HBS. subst as' bs'.
 exact(sf_relation_functional M SFMember(succM M a)(succM M b)closed shifted HClosed HShift).
Qed.
Print Assumptions source_finite_names_bound.
Print Assumptions source_finite_formulas_bound.
Print Assumptions source_named_member_vacuous.

