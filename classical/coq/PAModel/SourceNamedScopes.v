(** Finite stacks of named binders, represented by actual arithmetic maps.
    Stack length is finite at the metalevel; names and formula bounds are
    arbitrary elements of the PA model. Repeated names use the innermost entry. *)
From Stdlib Require Import List.
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension BetaPacking
  CodeExpressions NumericalProofs NumericalEnvironments NumericalContextRenaming NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps
  SourceBounded SourceRenamingBounds SourceRenamingIdentity.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Import ListNotations.
Unset Implicit Arguments.
Local Transparent holds.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Fixpoint named_scope_succ M (depth:nat) (i:carrier M) :=
  match depth with 0=>i | S d=>succM M (named_scope_succ M d i) end.
Fixpoint named_scope_index M (names:list (carrier M)) i v :=match names with
  | []=>v = i
  | x::tail=>(i = x /\v = zeroM M) \/
      (i<>x /\exists w,named_scope_index M tail i w /\v = succM M w)
  end.
Fixpoint named_scope_bound M (names:list (carrier M)) :=match names with
  | []=>zeroM M | x::tail=>succM M (addM M x (named_scope_bound M tail)) end.

Lemma named_scope_succ_add M depth i :
  named_scope_succ M depth i = addM M i (code_numeral M depth).
Proof.
  induction depth as [|d IH];cbn [named_scope_succ code_numeral].
  - symmetry. apply coding_add_zero_r.
  - rewrite IH,(Arithmetic.add_comm M i (succM M (code_numeral M d))),Arithmetic.add_succ.
    now rewrite Arithmetic.add_comm.
Qed.

Lemma named_scope_index_total M names i :exists v,named_scope_index M names i v.
Proof.
  induction names as [|x tail IH];cbn [named_scope_index].
  - exists i. reflexivity.
  - destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i x) as [E|NE].
    + exists (zeroM M). left;auto.
    + destruct IH as (v&HV). exists (succM M v). right. split;[exact NE|]. exists v. auto.
Qed.
Lemma named_scope_index_functional M names i v w :
  named_scope_index M names i v ->named_scope_index M names i w ->v = w.
Proof.
  revert v w. induction names as [|x tail IH];intros v w;cbn [named_scope_index].
  - congruence.
  - intros [[HX HV]|[HN (v'&HV&EV)]] [[HX' HW]|[HN' (w'&HW&EW)]];try congruence.
    rewrite EV,EW. f_equal. exact (IH v' w' HV HW).
Qed.
Lemma named_scope_index_bounded M names i v k :
  coding_lt M i k ->named_scope_index M names i v ->
  coding_lt M v (named_scope_succ M (length names) k).
Proof.
  revert v. induction names as [|x tail IH];intros v HI HV;cbn [named_scope_index] in HV.
  - subst v. exact HI.
  - cbn [length named_scope_succ]. destruct HV as [[_ ->]|[_ (w&HW&->)]].
    + apply coding_zero_lt_succ.
    + apply coding_lt_succ_cancel. exact (IH w HI HW).
Qed.
Lemma named_scope_member_bound M names x :In x names ->coding_lt M x (named_scope_bound M names).
Proof.
  induction names as [|y tail IH];cbn [In named_scope_bound];[tauto|].
  intros [->|HX];[apply coding_le_add|].
  apply (coding_lt_trans M x (named_scope_bound M tail)).
  - exact (IH HX).
  - rewrite Arithmetic.add_comm. apply coding_le_add.
Qed.
Lemma named_scope_index_default M names i v :
  (forall x,In x names ->i<>x) ->named_scope_index M names i v ->
  v = named_scope_succ M (length names) i.
Proof.
  revert v. induction names as [|x tail IH];intros v HN HV;cbn [named_scope_index] in HV.
  - exact HV.
  - destruct HV as [[E _]|[_ (w&HW&->)]].
    + exfalso. exact (HN x (or_introl eq_refl) E).
    + cbn [length named_scope_succ]. f_equal. apply (IH w);[|exact HW].
      intros y HY. exact (HN y (or_intror HY)).
Qed.

Fixpoint named_scope_index_formula_aux (names:list term) (lift:term->term) (i v:term) :form :=match names with
  | []=>v == i
  | x::tail=>((i == lift x)∧(v == zero))∨((i == lift x→⊥)∧
      ∃(named_scope_index_formula_aux tail (fun t=>(lift t)`[↑]) (i`[↑]) $0 ∧(v`[↑] == σ $0)))
  end.
Definition named_scope_index_formula names i v :=named_scope_index_formula_aux names (fun t=>t) i v.

Lemma named_scope_index_formula_aux_correct M names rho lift i v :
  holds M rho (named_scope_index_formula_aux names lift i v) <->
  named_scope_index M (map (fun t=>evalM M rho (lift t)) names) (evalM M rho i) (evalM M rho v).
Proof.
  revert rho lift i v. induction names as [|x tail IH];intros rho lift i v;
    cbn [named_scope_index_formula_aux map named_scope_index].
  - reflexivity.
  - rewrite holds_or,holds_and,holds_and,holds_imp,holds_ex.
    setoid_rewrite holds_and. setoid_rewrite IH.
    assert (HT:forall w,map (fun t=>evalM M (w .: rho) ((lift t)`[↑])) tail=
        map (fun t=>evalM M rho (lift t)) tail).
    { intro w. apply map_ext. intro t. unfold evalM. apply eval_up. }
    setoid_rewrite HT.
    setoid_rewrite substitution_holds_eq. setoid_rewrite substitution_holds_false.
    setoid_rewrite substitution_map_eval_succ.
    repeat setoid_rewrite substitution_eval_up. reflexivity.
Qed.
Lemma named_scope_index_formula_correct M names rho i v :
  holds M rho (named_scope_index_formula names i v) <->
  named_scope_index M (map (evalM M rho) names) (evalM M rho i) (evalM M rho v).
Proof. apply named_scope_index_formula_aux_correct. Qed.

Fixpoint named_scope_terms (n:nat) :list term :=match n with
  | 0=>[] |S k=>$0::map (fun t=>t`[↑]) (named_scope_terms k) end.
Fixpoint named_scope_environment M (names:list (carrier M)) :nat->carrier M :=match names with
  | []=>fun _=>zeroM M |x::tail=>x .: named_scope_environment M tail end.
Lemma named_scope_terms_correct M names :
  map (evalM M (named_scope_environment M names)) (named_scope_terms (length names)) = names.
Proof.
  induction names as [|x tail IH];cbn [named_scope_terms length named_scope_environment map].
  - reflexivity.
  - f_equal. rewrite map_map. transitivity (map (evalM M (named_scope_environment M tail)) (named_scope_terms (length tail)));[|exact IH].
    apply map_ext. intro t. unfold evalM. apply eval_up.
Qed.

Definition named_scope_map M names rb rc :=forall i v,
  renaming_lookup M rb rc (named_scope_bound M names) (code_numeral M (length names)) i v <->
    named_scope_index M names i v.

Theorem named_scope_map_total M names :exists rb rc,named_scope_map M names rb rc.
Proof.
  set (rho:=named_scope_environment M names).
  set (F:=named_scope_index_formula
    (map code_lift2 (named_scope_terms (length names))) $1 $0).
  assert (HF:forall i v,holds M (v .: i .: rho) F <->named_scope_index M names i v).
  { intros i v. unfold F. rewrite named_scope_index_formula_correct.
    assert (E:map (evalM M (v .: i .: rho)) (map code_lift2 (named_scope_terms (length names))) = names).
    { rewrite map_map. change (map (fun t=>evalM M (v .: i .: rho) (code_lift2 t)) (named_scope_terms (length names)) = names).
      setoid_rewrite code_eval_lift2. unfold rho. apply named_scope_terms_correct. }
    rewrite E. reflexivity. }
  set (n:=named_scope_bound M names).
  set (bound:=named_scope_succ M (length names) n).
  assert (HT:forall i,coding_lt M i n ->exists v,holds M (v .: i .: rho) F).
  { intros i _. destruct (named_scope_index_total M names i) as (v&HV). exists v. now apply HF. }
  assert (HB:forall i v,coding_lt M i n ->holds M (v .: i .: rho) F ->coding_lt M v bound).
  { intros i v HI HV. apply HF in HV. exact (named_scope_index_bounded M names i v n HI HV). }
  assert (HU:forall i v w,coding_lt M i n ->holds M (v .: i .: rho) F ->
      holds M (w .: i .: rho) F ->v = w).
  { intros i v w _ HV HW. apply HF in HV,HW. exact (named_scope_index_functional M names i v w HV HW). }
  assert (HB':forall i v,coding_lt M i n ->holds M (v .: i .: rho) F ->coding_lt M v (succM M bound)).
  { intros i v HI HV. exact (coding_lt_trans M v bound (succM M bound) (HB i v HI HV) (coding_lt_succ M bound)). }
  destruct (beta_pack_function M rho F n bound HT HB' HU) as (rb&rc&HBC).
  exists rb,rc. intros i v. split.
  - intros [[HI HV]|[HI EV]].
    + apply HF. exact (proj1 (HBC i v HI) HV).
    + assert (HN:forall x,In x names ->i<>x).
      { intros x HX E. subst i. exact (HI (named_scope_member_bound M names x HX)). }
      destruct (named_scope_index_total M names i) as (w&HW).
      pose proof (named_scope_index_default M names i w HN HW) as EW.
      rewrite named_scope_succ_add in EW. replace v with w by congruence. exact HW.
  - intro HV. destruct (environment_lt_cases M i n) as [HI|HI].
    + left. split;[exact HI|]. apply (proj2 (HBC i v HI)). now apply HF.
    + right. split;[exact HI|]. rewrite <-named_scope_succ_add.
      apply (named_scope_index_default M names i v);[|exact HV].
      intros x HX E. subst i. exact (HI (named_scope_member_bound M names x HX)).
Qed.

Print Assumptions named_scope_map_total.
