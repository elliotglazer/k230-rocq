(** Exact Cond(ps,x,y): Ord(x) implies x in y and piece closure in every level at x. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalInstantiation SourceHierarchySyntax SourceHierarchyFormula SourcePieceConjunction SourcePieceConjunctionFormula NumericalProofs.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_reflection_condition M domain level ordinal sb sc n x y out :=
  exists ord member lev pc point all both,
    numerical_instantiation M ordinal x ord /\sf_relation M SFMember x y member /\
    source_LL_instance M(succM M x)(zeroM M)lev /\
    source_piece_conjunction M domain level sb sc n(succM M y)(zeroM M)pc /\
    sf_relation M SFImpl lev pc point /\sf_relation M SFAll point(zeroM M)all /\
    sf_relation M SFAnd member all both /\sf_relation M SFImpl ord both out.

Definition condition_lift7(t:term):=t`[↑]`[↑]`[↑]`[↑]`[↑]`[↑]`[↑].
Lemma condition_eval_lift7 M rho a b c d e f g t :
  evalM M(a.:b.:c.:d.:e.:f.:g.:rho)(condition_lift7 t)=evalM M rho t.
Proof. unfold condition_lift7,evalM. now rewrite !eval_up. Qed.

Lemma condition_eval_var M rho idx : evalM M rho $(idx)=rho idx.
Proof. reflexivity. Qed.
Lemma condition_eval_zero M rho : evalM M rho zero=zeroM M.
Proof. reflexivity. Qed.
Lemma condition_eval_succ M rho t : evalM M rho (σ t)=succM M(evalM M rho t).
Proof. reflexivity. Qed.

Definition source_reflection_condition_formula(domain level ordinal sb sc n x y out:term):form:=
  ∃∃∃∃∃∃∃(
    numerical_instantiation_formula(condition_lift7 ordinal)(condition_lift7 x)$6 ∧
    sf_formula SFMember(condition_lift7 x)(condition_lift7 y)$5 ∧
    source_LL_instance_formula(σ(condition_lift7 x))zero $4 ∧
    source_piece_conjunction_formula(condition_lift7 domain)(condition_lift7 level)
      (condition_lift7 sb)(condition_lift7 sc)(condition_lift7 n)(σ(condition_lift7 y))zero $3 ∧
    sf_formula SFImpl $4 $3 $2 ∧sf_formula SFAll $2 zero $1 ∧
    sf_formula SFAnd $5 $1 $0 ∧sf_formula SFImpl $6 $0(condition_lift7 out)).
Local Opaque holds numerical_instantiation_formula sf_formula source_LL_instance_formula source_piece_conjunction_formula.

Theorem source_reflection_condition_formula_correct M rho domain level ordinal sb sc n x y out :
  holds M rho(source_reflection_condition_formula domain level ordinal sb sc n x y out) <->
  source_reflection_condition M(evalM M rho domain)(evalM M rho level)(evalM M rho ordinal)
    (evalM M rho sb)(evalM M rho sc)(evalM M rho n)(evalM M rho x)(evalM M rho y)(evalM M rho out).
Proof.
  unfold source_reflection_condition_formula,source_reflection_condition.
  repeat setoid_rewrite NumericalProofs.holds_ex. repeat setoid_rewrite NumericalProofs.holds_and.
  setoid_rewrite numerical_instantiation_formula_correct. setoid_rewrite sf_formula_correct.
  setoid_rewrite source_LL_instance_formula_correct. setoid_rewrite source_piece_conjunction_formula_correct.
  setoid_rewrite condition_eval_succ. setoid_rewrite condition_eval_zero.
  setoid_rewrite condition_eval_var. setoid_rewrite condition_eval_lift7.
  split;intros(a&b&c&d&e&f&g&H);exists a,b,c,d,e,f,g;cbn in *;tauto.
Qed.

Theorem source_reflection_condition_total M domain level ordinal sb sc n x y :
  exists out,source_reflection_condition M domain level ordinal sb sc n x y out.
Proof.
  destruct(numerical_instantiation_total M ordinal x) as(ord&HO).
  destruct(sf_relation_total M SFMember x y) as(member&HM).
  destruct(source_LL_instance_total M(succM M x)(zeroM M)) as(lev&HL).
  destruct(source_piece_conjunction_total M domain level sb sc n(succM M y)(zeroM M)) as(pc&HP).
  destruct(sf_relation_total M SFImpl lev pc) as(point&HPoint).
  destruct(sf_relation_total M SFAll point(zeroM M)) as(all&HA).
  destruct(sf_relation_total M SFAnd member all) as(both&HB).
  destruct(sf_relation_total M SFImpl ord both) as(out&HOut).
  exists out,ord,member,lev,pc,point,all,both. repeat split;assumption.
Qed.

Theorem source_reflection_condition_functional M domain level ordinal sb sc n x y out out' :
  source_reflection_condition M domain level ordinal sb sc n x y out ->
  source_reflection_condition M domain level ordinal sb sc n x y out' ->out=out'.
Proof.
  intros(o&m&l&p&q&a&b&HO&HM&HL&HP&HQ&HA&HB&HOut)
    (o'&m'&l'&p'&q'&a'&b'&HO'&HM'&HL'&HP'&HQ'&HA'&HB'&HOut').
  assert(E:o'=o) by(eapply numerical_instantiation_functional;eassumption). subst o'.
  assert(E:m'=m) by(eapply sf_relation_functional;eassumption). subst m'.
  assert(E:l'=l) by(eapply source_LL_instance_functional;eassumption). subst l'.
  assert(E:p'=p) by(eapply source_piece_conjunction_functional;eassumption). subst p'.
  assert(E:q'=q) by(eapply sf_relation_functional;eassumption). subst q'.
  assert(E:a'=a) by(eapply sf_relation_functional;eassumption). subst a'.
  assert(E:b'=b) by(eapply sf_relation_functional;eassumption). subst b'.
  eapply sf_relation_functional;eassumption.
Qed.

Print Assumptions source_reflection_condition_formula_correct.
Print Assumptions source_reflection_condition_total.
Print Assumptions source_reflection_condition_functional.
