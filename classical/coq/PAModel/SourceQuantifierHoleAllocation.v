(** Allocate actual named and two-scope matrix holes for an arbitrary
    internally coded quantified body. Fresh role bounds remain explicit. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking CodeExpressions SourceBounded SourceRenamingBounds
 NumericalRenamingMaps NumericalRenaming SourceQuantifierMatrixScopes SourceSetRelativization SourceSetRelativizationBounds SourceNamedScopes SourceNamedScopeBinding.
From FOL.Tennenbaum Require Peano.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Lemma source_index_below_fresh_bound M k a i:
 coding_lt M i(succM M k)->~coding_lt M a(succM M k)->coding_lt M i(succM M a).
Proof.
 intros HI HA.
 destruct(@Peano.trichotomy(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i a)as[H|[H|H]].
 - exact(coding_lt_trans M i a(succM M a)H(coding_lt_succ M a)).
 - subst i. apply coding_lt_succ.
 - exfalso. exact(HA(coding_lt_trans M a i(succM M k)H HI)).
Qed.
Theorem source_first_value_matrix_bound M f named k a:
 source_bounded M f k->~coding_lt M a(succM M k)->source_first_value_matrix M a f named->source_bounded M named(succM M a).
Proof.
 intros BF HA HNamed. apply(numerical_renaming_preserves_bound M f a a(code_numeral M 1)(code_numeral M 1)named k(succM M a)BF HNamed).
 intros i j HI HJ.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[q ->]].
 - rewrite(renaming_lookup_functional M _ _ _ _(zeroM M)j a HJ(source_one_role_zero_lookup M a(code_numeral M 1))). apply coding_lt_succ.
 - assert(HN:succM M q<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M q(eq_sym E))).
   rewrite(renaming_lookup_functional M _ _ _ _ _ j _ HJ(source_one_role_positive_lookup M a(code_numeral M 1)(succM M q)HN)).
   rewrite<-Arithmetic.succ_as_add.
   exact(source_index_below_fresh_bound M k a(succM M(succM M q))(proj2(coding_lt_succ_cancel M(succM M q)k)HI)HA).
Qed.
Theorem source_quantifier_holes_total M f k a e:
 source_bounded M f k->coding_lt M(zeroM M)k->~coding_lt M a(succM M k)->~coding_lt M e(succM M k)->a<>e->
 exists named theta child parent childrelative parentrelative,
 source_first_value_matrix M a f named/\source_set_relativization M(code_numeral M 1)named theta/\
 source_quantifier_matrix M(code_numeral M 1)f child/\source_quantifier_matrix M(zeroM M)f parent/\
 source_set_relativization M(code_numeral M 3)child childrelative/\source_set_relativization M(code_numeral M 3)parent parentrelative/\
 named_scope_renaming M[e;a]theta childrelative/\named_scope_renaming M[a;e]theta parentrelative/\
 source_bounded M named(succM M a)/\source_bounded M theta(succM M a).
Proof.
 intros BF HK HA HE HAE.
 destruct(numerical_renaming_total M f a a(code_numeral M 1)(code_numeral M 1))as(named&HNamed).
 destruct(source_set_relativization_total M(code_numeral M 1)named)as(theta&HTheta).
 destruct(numerical_renaming_total M f(code_numeral M 1)(code_numeral M 1)(code_numeral M 1)(code_numeral M 3))as(child&HChild).
 destruct(numerical_renaming_total M f(zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 3))as(parent&HParent).
 destruct(source_quantifier_relative_scopes M f named theta child parent a e k BF HK HA HE HAE HNamed HTheta HChild HParent)
  as(childrelative&parentrelative&HC&HP&HCR&HPR).
 pose proof(source_first_value_matrix_bound M f named k a BF HA HNamed)as BN.
 assert(HOne:coding_lt M(code_numeral M 1)(succM M a)).
 { apply(source_index_below_fresh_bound M k a(code_numeral M 1));[|exact HA]. exact(proj2(coding_lt_succ_cancel M(zeroM M)k)HK). }
 exists named,theta,child,parent,childrelative,parentrelative.
 exact(conj HNamed(conj HTheta(conj HChild(conj HParent(conj HCR(conj HPR(conj HC(conj HP(conj BN
  (source_set_relativization_preserves_bound M named(code_numeral M 1)(succM M a)theta HOne BN HTheta)))))))))).
Qed.
Print Assumptions source_first_value_matrix_bound.
Print Assumptions source_quantifier_holes_total.
