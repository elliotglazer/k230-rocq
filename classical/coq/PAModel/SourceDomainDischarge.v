(** Eliminate an internally finite domain table by actual source ExE,
    using PA induction on the table length. No proof substitution is needed. *)
From PAModel Require Import Model CodeExpressions FiniteCoding NumericalProofs
  NumericalContexts NumericalEnvironments NumericalContextRenaming SourceBounded
  SourceBoundMonotone SourceSequents SetFormulaCodes SourceQuantifierRules
  NumericalSourceFull SourceDomainContexts SourceProofWeakening SourceClosedShift.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Theorem source_domain_context_representation_included M domain k b c u v :
  source_domain_context M domain k b c -> source_domain_context M domain k u v ->
  context_included M b c k u v k.
Proof.
  intros HS HT f HF.
  apply (proj2 (source_domain_context_member_iff M domain k u v f HT)).
  exact (proj1 (source_domain_context_member_iff M domain k b c f HS) HF).
Qed.

Definition source_domain_discharge_at M domain f k := forall b c,
  source_domain_context M domain k b c -> source_full_prv M b c k f ->
  source_full_prv M (zeroM M) (zeroM M) (zeroM M) f.
Definition source_domain_discharge_formula : form :=
  ∀∀ (source_domain_context_formula $3 $2 $1 $0 →
    source_full_prv_formula $1 $0 $2 $4 → source_full_prv_formula zero zero zero $4).
Local Opaque holds source_domain_context_formula source_full_prv_formula.

Theorem source_domain_discharge_definable M domain f :
  Definable1 M (source_domain_discharge_at M domain f).
Proof.
  exists source_domain_discharge_formula,(domain .: f .: fun _=>zeroM M). intro k.
  unfold source_domain_discharge_formula,source_domain_discharge_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_domain_context_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. reflexivity.
Qed.

Theorem source_domain_table_discharge M domain ex f :
  source_bounded M domain (code_numeral M 1) ->
  sf_relation M SFEx domain (zeroM M) ex ->
  source_full_prv M (zeroM M) (zeroM M) (zeroM M) ex ->
  source_bounded M f (zeroM M) ->
  forall k b c,source_domain_context M domain k b c -> source_full_prv M b c k f ->
  source_full_prv M (zeroM M) (zeroM M) (zeroM M) f.
Proof.
  intros HD HEx PEx HF.
  apply (definable_induction M (source_domain_discharge_at M domain f)
    (source_domain_discharge_definable M domain f)).
  - intros b c HT P.
    apply (source_full_prv_weaken_bounded M b c (zeroM M)
      (zeroM M) (zeroM M) (zeroM M) f (zeroM M) P).
    + intros a HA. exfalso. exact (context_empty M b c a HA).
    + apply context_bounded_empty.
  - intros k IH b c HT P.
    destruct (source_domain_context_total M domain k) as [tb [tc HTable]].
    destruct (context_shift_total M tb tc k) as [sb [sc HShift]].
    destruct (environment_cons_total M sb sc k domain) as [db [dc [dn HCons]]].
    assert (EN:dn=succM M k) by exact (proj1 HCons). subst dn.
    pose proof (source_domain_context_cons_shift M domain k tb tc sb sc db dc
      (succM M k) HD HTable HShift HCons) as HCanonical.
    assert (PBranch:source_full_prv M db dc (succM M k) f).
    { apply (source_full_prv_weaken_bounded M b c (succM M k) db dc (succM M k) f
        (succM M k) P).
      - exact (source_domain_context_representation_included M domain (succM M k) b c db dc HT HCanonical).
      - exact (source_domain_context_bounded M domain (succM M k) db dc HD HCanonical). }
    assert (PExist:source_full_prv M tb tc k ex).
    { apply (source_full_prv_weaken_bounded M (zeroM M) (zeroM M) (zeroM M)
        tb tc k ex k PEx).
      - intros a HA. exfalso. exact (context_empty M (zeroM M) (zeroM M) a HA).
      - exact (source_domain_context_bounded M domain k tb tc HD HTable). }
    apply (IH tb tc HTable).
    apply (full_source_ExE M tb tc k domain ex f f sb sc db dc (succM M k)).
    + exists k. split.
      * exact (source_bounded_monotone M f (zeroM M) k HF (coding_zero_lt_succ M k)).
      * exact (source_domain_context_bounded M domain k tb tc HD HTable).
    + exact PExist.
    + exact PBranch.
    + exact HEx.
    + exact HShift.
    + exact HCons.
    + exact (source_closed_shift_self M f HF).
Qed.

Print Assumptions source_domain_context_representation_included.
Print Assumptions source_domain_discharge_definable.
Print Assumptions source_domain_table_discharge.
