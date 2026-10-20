(** Repeated proof-producing specialization of a finite universal prefix. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  ProofTemplates NamedLeibnizSteps QuotientAtomTemplates FiniteTemplateSpecialization
  TemplateBinderFresh.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Fixpoint template_all_prefix {ff} n
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :=
  match n with 0 => phi | S m => quant All (template_all_prefix m phi) end.
Fixpoint template_bind_arguments (args : list code_expr) (env : nat -> code_expr) :=
  match args with []=>env | a::rest=>template_bind_arguments rest (a .: env) end.
Fixpoint template_advance_fresh fresh n :=
  match n with 0=>fresh | S m=>template_advance_fresh (CEadd fresh (CEconst 1)) m end.
Fixpoint template_advance_name M k n :=
  match n with 0=>k | S m=>template_advance_name M (succM M k) m end.

Lemma template_advance_fresh_graph M n : forall rho fresh k,
  code_relation M rho fresh k ->
  code_relation M rho (template_advance_fresh fresh n) (template_advance_name M k n).
Proof.
  induction n;intros rho fresh k HK;cbn;[exact HK|].
  apply IHn,template_fresh_increment_graph,HK.
Qed.

Lemma template_advance_name_above M n : forall y k,
  coding_lt M y k -> coding_lt M y (template_advance_name M k n).
Proof.
  induction n;intros y k HK;cbn;[exact HK|].
  apply IHn. exact (coding_lt_trans M y k (succM M k) HK (coding_lt_succ M k)).
Qed.

Theorem finite_template_specialize_list M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall args rho env eta fresh k,
  (forall idx,code_relation M rho (env idx) (eta idx)) ->
  (forall idx,coding_lt M (eta idx) k) ->
  code_relation M rho fresh k -> coding_lt M (zeroM M) k ->
  (forall term,In term args -> exists y,code_relation M rho term y /\ coding_lt M y k) ->
  ns_proof M rho (template_set_formula env fresh (template_all_prefix (length args) phi)) ->
  ns_proof M rho (template_set_formula (template_bind_arguments args env)
    (template_advance_fresh fresh (length args)) phi).
Proof.
  induction args as [|term args IH];intros rho env eta fresh k HE HL HK H0 HA HP.
  - exact HP.
  - destruct (HA term (or_introl eq_refl)) as [y [HY HYlt]].
    apply (IH rho (term .: env) (y .: eta) (CEadd fresh (CEconst 1)) (succM M k)).
    + intros [|idx];cbn;[exact HY|apply HE].
    + intros [|idx];cbn.
      * exact (coding_lt_trans M y k (succM M k) HYlt (coding_lt_succ M k)).
      * exact (coding_lt_trans M (eta idx) k (succM M k) (HL idx) (coding_lt_succ M k)).
    + now apply template_fresh_increment_graph.
    + exact (coding_lt_trans M (zeroM M) k (succM M k) H0 (coding_lt_succ M k)).
    + intros t Ht. destruct (HA t (or_intror Ht)) as [z [HZ HZlt]].
      exists z;split;[exact HZ|].
      exact (coding_lt_trans M z k (succM M k) HZlt (coding_lt_succ M k)).
    + exact (finite_template_specialize M (template_all_prefix (length args) phi)
        rho env eta fresh k term y HE HL HK HY H0 HYlt HP).
Qed.

Print Assumptions template_advance_fresh_graph.
Print Assumptions template_advance_name_above.
Print Assumptions finite_template_specialize_list.
