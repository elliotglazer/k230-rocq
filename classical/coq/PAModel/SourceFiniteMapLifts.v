(** Metafinitely many actual binder lifts. This exposes both fixed bound
    indices and shifted arbitrary model-valued tail indices. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  NumericalSubstitutionMaps NumericalSubstitution SubstitutionSource SourceFiniteCutoffShift SourceNamedScopes.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Fixpoint source_substitution_lifts M depth b c n base db dc dn :=match depth with
  | 0=>db=b /\dc=c /\dn=n
  | S d=>exists ub uc un,source_substitution_lifts M d b c n base ub uc un /\
      substitution_lift M ub uc un (named_scope_succ M d base) db dc dn
  end.

Theorem source_substitution_lifts_total M depth b c n base :
  exists db dc dn,source_substitution_lifts M depth b c n base db dc dn.
Proof.
  induction depth as [|d (ub&uc&un&HI)].
  - exists b,c,n. repeat split;reflexivity.
  - destruct (substitution_lift_total M ub uc un (named_scope_succ M d base)) as (db&dc&dn&HL).
    exists db,dc,dn,ub,uc,un. auto.
Qed.

Theorem source_substitution_lifts_tail M depth b c n base db dc dn i v :
  source_substitution_lifts M depth b c n base db dc dn ->substitution_lookup M b c n base i v ->
  substitution_lookup M db dc dn (named_scope_succ M depth base)
    (named_scope_succ M depth i) (named_scope_succ M depth v).
Proof.
  revert db dc dn. induction depth as [|d IH];intros db dc dn HL HV.
  - destruct HL as [-> [-> ->]]. exact HV.
  - destruct HL as (ub&uc&un&HI&HS). cbn [named_scope_succ].
    apply (proj2 (substitution_lift_tail M ub uc un (named_scope_succ M d base)
      db dc dn (named_scope_succ M d i) (named_scope_succ M d v) HS)).
    exact (IH ub uc un HI HV).
Qed.

Theorem source_substitution_lifts_head M depth b c n base db dc dn j :
  (j<depth)%nat ->source_substitution_lifts M depth b c n base db dc dn ->
  substitution_lookup M db dc dn (named_scope_succ M depth base) (code_numeral M j) (code_numeral M j).
Proof.
  revert db dc dn j. induction depth as [|d IH];intros db dc dn j HJ HL;[lia|].
  destruct HL as (ub&uc&un&HI&HS). destruct j as [|j].
  - exact (proj2 (substitution_lift_head M ub uc un (named_scope_succ M d base)
      db dc dn (zeroM M) HS) eq_refl).
  - apply (proj2 (substitution_lift_tail M ub uc un (named_scope_succ M d base)
      db dc dn (code_numeral M j) (code_numeral M j) HS)).
    exact (IH ub uc un j ltac:(lia) HI).
Qed.

Lemma named_scope_succ_zero M depth :named_scope_succ M depth (zeroM M)=code_numeral M depth.
Proof. induction depth as [|d IH];cbn [named_scope_succ code_numeral];[reflexivity|now rewrite IH]. Qed.
Lemma named_scope_succ_succ M depth i :
  named_scope_succ M depth (succM M i)=succM M (named_scope_succ M depth i).
Proof. induction depth as [|d IH];cbn [named_scope_succ];[reflexivity|now rewrite IH]. Qed.

Theorem source_cutoff_shift_tail M depth b c n i :source_cutoff_shift_map M depth b c n ->
  substitution_lookup M b c n (code_numeral M (S depth))
    (named_scope_succ M depth i) (named_scope_succ M (S depth) i).
Proof.
  revert b c n. induction depth as [|d IH];intros b c n HM.
  - destruct HM as [-> [-> ->]]. apply source_cutoff_shift_base_lookup.
  - destruct HM as (ub&uc&un&HI&HL). cbn [named_scope_succ].
    apply (proj2 (substitution_lift_tail M ub uc un (code_numeral M (S d)) b c n
      (named_scope_succ M d i) (succM M (named_scope_succ M d i)) HL)).
    exact (IH ub uc un HI).
Qed.

Theorem source_cutoff_shift_head M depth b c n j :
  (j<depth)%nat ->source_cutoff_shift_map M depth b c n ->
  substitution_lookup M b c n (code_numeral M (S depth)) (code_numeral M j) (code_numeral M j).
Proof.
  revert b c n j. induction depth as [|d IH];intros b c n j HJ HM;[lia|].
  destruct HM as (ub&uc&un&HI&HL). destruct j as [|j].
  - exact (proj2 (substitution_lift_head M ub uc un (code_numeral M (S d))
      b c n (zeroM M) HL) eq_refl).
  - apply (proj2 (substitution_lift_tail M ub uc un (code_numeral M (S d))
      b c n (code_numeral M j) (code_numeral M j) HL)).
    exact (IH ub uc un j ltac:(lia) HI).
Qed.

Print Assumptions source_substitution_lifts_total.
Print Assumptions source_substitution_lifts_tail.
Print Assumptions source_cutoff_shift_tail.
