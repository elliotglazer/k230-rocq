(** Ordinary source proof composition for the existential witness shells.
    These wrappers retain the internally coded calculus and closed ZFR
    axiom contexts; none appeals to semantic completeness. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes
  SourceBounded SourceBoundMonotone SourceTraceBounds NumericalContexts NumericalSourceFull NumericalRenaming
  SourceQuantifierRules SourceExistsImplication SourcePropositionalTemplates SourceFiniteProofContexts
  SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_zfr_provable_has_bound M f :source_zfr_provable M f ->exists k,source_bounded M f k.
Proof. intros(b&c&n&HC&HP). destruct(source_full_prv_wellformed M b c n f HP) as(k&HB&HCtx). now exists k. Qed.

Theorem source_implication_shift_graph M a b f a' b' f' :
  sf_relation M SFImpl a b f ->sf_relation M SFImpl a' b' f' ->
  source_formula_shift M a a' ->source_formula_shift M b b' ->source_formula_shift M f f'.
Proof.
  intros HF HF' HA HB. apply(proj2(numerical_renaming_binary M SFImpl a b f
    (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)f'(or_intror(or_intror eq_refl))HF)).
  exists a',b'. repeat split;assumption.
Qed.

Theorem source_zfr_all_proof M f all :source_zfr_provable M f ->sf_relation M SFAll f(zeroM M)all ->
  source_zfr_provable M all.
Proof.
  intros HP HG. apply(proj1(source_zfr_descriptor_provable M all)).
  exact(source_descriptor_provable_all M ZFRSourceDescriptor f all
    (proj2(source_zfr_descriptor_provable M f)HP)HG).
Qed.

Theorem source_zfr_exists_implication M body ex target shifted witnessimp result k l :
  source_bounded M ex k ->source_bounded M target l ->sf_relation M SFEx body(zeroM M)ex ->
  source_formula_shift M target shifted ->sf_relation M SFImpl body shifted witnessimp ->
  sf_relation M SFImpl ex target result ->source_zfr_provable M witnessimp ->source_zfr_provable M result.
Proof.
  intros HB HT HE HS HW HR(b&c&n&HC&HP).
  pose proof(proj2(source_zfr_descriptor_context M b c n)HC) as HAC.
  exists b,c,n. split;[exact HC|].
  apply(source_full_exists_implication M b c n(addM M k l)body ex target shifted witnessimp result).
  - exact(proj1 HAC).
  - exact(source_bounded_monotone M ex k(addM M k l)HB(coding_le_add M k l)).
  - apply(source_bounded_monotone M target l(addM M k l)HT). rewrite Arithmetic.add_comm. apply coding_le_add.
  - exact HE.
  - exact HS.
  - exact HW.
  - exact HR.
  - exact HP.
Qed.

Theorem source_zfr_prop_one M a d (program:source_prop_program[a]d) rho k old result :
  (forall i,source_bounded M(rho i)k) ->
  code_relation M rho(source_prop_expression a)old ->code_relation M rho(source_prop_expression d)result ->
  source_zfr_provable M old ->source_zfr_provable M result.
Proof.
  intros HB HO HR(b&c&n&HC&HP). exists b,c,n. split;[exact HC|].
  pose proof(proj2(source_zfr_descriptor_context M b c n)HC) as HAC.
  apply(source_prop_program_sound M[a]d program rho k b c n result HB).
  - exact(context_bounded_monotone M b c n(zeroM M)k(proj1 HAC)(coding_zero_lt_succ M k)).
  - intros f[<-|[]] out HG.
    pose proof(code_relation_functional M(source_prop_expression a)rho out old HG HO) as E. now subst out.
  - exact HR.
Qed.

Theorem source_zfr_prop_two M a b d (program:source_prop_program[a;b]d) rho k first second result :
  (forall i,source_bounded M(rho i)k) ->
  code_relation M rho(source_prop_expression a)first ->code_relation M rho(source_prop_expression b)second ->
  code_relation M rho(source_prop_expression d)result ->
  source_zfr_provable M first ->source_zfr_provable M second ->source_zfr_provable M result.
Proof.
  intros HB HF HS HR PF PS.
  assert(Premises:forall f,In f[first;second] ->source_descriptor_provable M ZFRSourceDescriptor f).
  { intros f[<-|[<-|[]]];apply(proj2(source_zfr_descriptor_provable M _));assumption. }
  destruct(source_descriptor_finite_common_context M ZFRSourceDescriptor _ Premises) as(ub&uc&un&HC&P).
  exists ub,uc,un. split;[exact(proj1(source_zfr_descriptor_context M ub uc un)HC)|].
  apply(source_prop_program_sound M[a;b]d program rho k ub uc un result HB).
  - exact(context_bounded_monotone M ub uc un(zeroM M)k(proj1 HC)(coding_zero_lt_succ M k)).
  - intros f[<-|[<-|[]]]out HG.
    + pose proof(code_relation_functional M(source_prop_expression a)rho out first HG HF) as E.
      subst out. apply P. now left.
    + pose proof(code_relation_functional M(source_prop_expression b)rho out second HG HS) as E.
      subst out. apply P. right. now left.
  - exact HR.
Qed.

Print Assumptions source_zfr_exists_implication.
Print Assumptions source_zfr_prop_one.
Print Assumptions source_zfr_prop_two.
Print Assumptions source_implication_shift_graph.
