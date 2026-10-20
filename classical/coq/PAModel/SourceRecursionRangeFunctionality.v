(** Close all three functionality quantifiers for literal RR, retaining its ordinary background. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceQuantifierRules
 SourceFiniteTelescope SourceFiniteTelescopeQuantifier SourceRecursionRangeRelation SourceRecursionRangeBackground SourceRecursionRangeEquality
 SourceRecursionExtensionInputShift SourceRecursionExAAdjoin SourceFunctionalityShells SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_rr_functionality_named M phi o a N A ra rb functionality law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->source_rec_rr_background M phi o N A ->
 source_rec_rr M phi(code_numeral M 2)(code_numeral M 1)(succM M(succM M(succM M o)))(succM M(succM M(succM M a)))(succM M(succM M(succM M N)))ra ->
 source_rec_rr M phi(code_numeral M 2)(zeroM M)(succM M(succM M(succM M o)))(succM M(succM M(succM M a)))(succM M(succM M(succM M N)))rb ->
 source_functionality_graph M ra rb functionality ->source_finite_telescope M A functionality law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN HA HRA HRB HF HLaw. set(s:=succM M).
 destruct(source_rec_rr_background_total M phi(s o)(s N))as(A1&HA1).
 destruct(source_rec_rr_background_total M phi(s(s o))(s(s N)))as(A2&HA2).
 destruct(source_rec_rr_background_total M phi(s(s(s o)))(s(s(s N))))as(A3&HA3).
 pose proof(source_rec_rr_background_shift M phi o N A A1 BP HA HA1)as S1.
 pose proof(source_rec_rr_background_shift M phi(s o)(s N)A1 A2 BP HA1 HA2)as S2.
 pose proof(source_rec_rr_background_shift M phi(s(s o))(s(s N))A2 A3 BP HA2 HA3)as S3.
 pose proof(source_rec_rr_background_bounded M phi o N A k BP BO BN HA)as Bounds.
 pose proof(source_finite_shifted_bounds M A A1 k S1 Bounds)as Bounds1.
 pose proof(source_finite_shifted_bounds M A1 A2(s k)S2 Bounds1)as Bounds2.
 destruct(sf_relation_total M SFEqual(code_numeral M 1)(zeroM M))as(equal&HE).
 destruct(source_functionality_shell M ra rb equal functionality HE HF)as(rhs&point&one&two&HR&HP&H1&H2&H3).
 pose proof(source_rec_rr_bounded M phi(code_numeral M 2)(code_numeral M 1)(s(s(s o)))(s(s(s a)))(s(s(s N)))ra(s(s(s k)))BP
  ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HRA)as BRA.
 pose proof(source_rec_rr_bounded M phi(code_numeral M 2)(zeroM M)(s(s(s o)))(s(s(s a)))(s(s(s N)))rb(s(s(s k)))BP
  ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HRB)as BRB.
 assert(BE:source_bounded M equal(s(s(s k)))).
 { apply(proj2(source_bounded_accept_atom M SFEqual(code_numeral M 1)(zeroM M)equal(s(s(s k)))(or_intror eq_refl)HE)). split;rec_exa_name_bound. }
 pose proof(proj2(source_bounded_accept_binary M SFImpl rb equal rhs(s(s(s k)))(or_intror(or_intror eq_refl))HR)(conj BRB BE))as BR.
 pose proof(proj2(source_bounded_accept_binary M SFImpl ra rhs point(s(s(s k)))(or_intror(or_intror eq_refl))HP)(conj BRA BR))as BPoint.
 pose proof(proj2(source_bounded_accept_unary M SFAll point one(s(s k))(or_introl eq_refl)H1)BPoint)as BOne.
 pose proof(proj2(source_bounded_accept_unary M SFAll one two(s k)(or_introl eq_refl)H2)BOne)as BTwo.
 destruct(source_finite_telescope_total M A3 point)as(pointLaw&HPointLaw).
 assert(PPoint:source_zfr_provable M pointLaw).
 { destruct HA3 as(funlaw&totality&induction&member&E&HFun&HT&HI&HM). subst A3.
   assert(HTel:source_finite_telescope M[funlaw;totality;induction;member;ra;rb]equal pointLaw).
   { apply(source_finite_telescope_prefix M[funlaw;totality;induction;member][ra;rb]point equal pointLaw HPointLaw).
     exists rhs. split;[exists equal;split;[reflexivity|exact HR]|exact HP]. }
   apply(source_zfr_rec_rr_equality M phi(s(s(s o)))(s(s(s a)))(s(s(s N)))(code_numeral M 2)(code_numeral M 1)(zeroM M)
    funlaw totality induction member ra rb equal pointLaw(s(s(s k))));try rec_exa_name_bound;assumption. }
 destruct(source_finite_telescope_total M A2 one)as(oneLaw&HOneLaw).
 pose proof(source_zfr_finite_telescope_all M A2 A3 point one pointLaw oneLaw(s(s k))Bounds2 BPoint S3 H1 HPointLaw HOneLaw PPoint)as POne.
 destruct(source_finite_telescope_total M A1 two)as(twoLaw&HTwoLaw).
 pose proof(source_zfr_finite_telescope_all M A1 A2 one two oneLaw twoLaw(s k)Bounds1 BOne S2 H2 HOneLaw HTwoLaw POne)as PTwo.
 exact(source_zfr_finite_telescope_all M A A1 two functionality twoLaw law k Bounds BTwo S1 H3 HTwoLaw HLaw PTwo).
Qed.
Print Assumptions source_zfr_rec_rr_functionality_named.
