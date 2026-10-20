(** Actual capture-avoiding substitution and shift of Clos. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution
  SourceQuantifierRules SourceRecursionBinaryInstance SourceRecursionBinaryGraphTransport
  SourceRecursionAttemptTransport SourceRecursionShiftGraphs SourceRecursionClosureSyntax.
Unset Implicit Arguments.

Theorem source_rec_closure_substitution M phi a Y old a' Y' new rb rc rn base:
  source_bounded M phi(code_numeral M 2) ->
  source_rec_closure M phi a Y old ->source_rec_closure M phi a' Y' new ->
  substitution_lookup M rb rc rn base a a' ->substitution_lookup M rb rc rn base Y Y' ->
  numerical_substitution M old rb rc rn base new.
Proof.
  intros BP(i&g&b&m&d&e&p&f&HI&HG&HB&HM&HD&HE&HP&HF&HO)
    (i'&g'&b'&m'&d'&e'&p'&f'&HI'&HG'&HB'&HM'&HD'&HE'&HP'&HF'&HO')HA HY.
  destruct(substitution_lift_total M rb rc rn base)as(b1&c1&n1&L1).
  destruct(substitution_lift_total M b1 c1 n1(succM M base))as(b2&c2&n2&L2).
  pose proof(proj1(proj2 L1))as Z1.
  pose proof(proj2(proj2 L1)_ _ HY)as Y1.
  pose proof(proj1(proj2 L2))as Z2.
  pose proof(proj2(proj2 L2)_ _ Z1)as O2.
  pose proof(proj2(proj2 L2)_ _ Y1)as Y2.
  assert(SI:numerical_substitution M i rb rc rn base i').
  { apply(proj2(numerical_substitution_member M a Y i rb rc rn base i' HI)). exists a',Y'. auto. }
  assert(SG:numerical_substitution M g b1 c1 n1(succM M base)g').
  { apply(proj2(numerical_substitution_member M _ _ g b1 c1 n1(succM M base)g' HG)).
    exists(zeroM M),(succM M Y'). auto. }
  assert(SM:numerical_substitution M m b2 c2 n2(succM M(succM M base))m').
  { apply(proj2(numerical_substitution_member M _ _ m b2 c2 n2(succM M(succM M base))m' HM)).
    exists(zeroM M),(succM M(succM M Y')). auto. }
  pose proof(source_rec_binary_substitution_graph M phi(code_numeral M 1)(zeroM M)b
    (code_numeral M 1)(zeroM M)b' b2 c2 n2(succM M(succM M base))BP HB HB' O2 Z2)as SB.
  assert(SEx:numerical_substitution M e b1 c1 n1(succM M base)e').
  { apply(proj2(numerical_substitution_quantifier M false d e b1 c1 n1(succM M base)e' HE)).
    exists b2,c2,n2,d'. split;[exact L2|]. split;[attempt_substitution|exact HE']. }
  assert(SAll:numerical_substitution M f rb rc rn base f').
  { apply(proj2(numerical_substitution_quantifier M true p f rb rc rn base f' HF)).
    exists b1,c1,n1,p'. split;[exact L1|]. split;[attempt_substitution|exact HF']. }
  attempt_substitution.
Qed.

Theorem source_rec_closure_shift M phi a Y old new:
  source_bounded M phi(code_numeral M 2) ->
  source_rec_closure M phi a Y old ->source_rec_closure M phi(succM M a)(succM M Y)new ->
  source_formula_shift M old new.
Proof.
  intros BP HO HN.
  apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
  rewrite Arithmetic.add_zero. exact(source_rec_closure_substitution M phi a Y old(succM M a)(succM M Y)new
    (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)BP HO HN(source_rec_shift_lookup M a)(source_rec_shift_lookup M Y)).
Qed.
Print Assumptions source_rec_closure_substitution.
Print Assumptions source_rec_closure_shift.
