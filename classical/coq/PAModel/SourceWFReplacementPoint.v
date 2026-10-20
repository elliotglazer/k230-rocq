(** Under the output-domain guard, the raw and guarded existential profiles
    are equivalent. Both directions retain the same input witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalSourceFull SourceQuantifierRules
  SourceDerivedRules SourceConjunctionRules SourceContextProofHelpers
  SourcePropositionalTemplates SourceWFReplacementBody SourceWFReplacementExistential.
Unset Implicit Arguments.

Theorem source_full_wf_rep_guarded_point M b c n k domain domain1 input theta rawbody targetbody rawex targetex
    left rawforward rawreverse rawpoint forward reverse targetpoint guardpoint :
  (forall i,source_bounded M (wf_rep_env domain domain1 input theta i) (succM M k)) ->
  context_bounded M b c n k ->source_bounded M domain k ->source_bounded M left k ->
  source_formula_shift M domain domain1 ->
  code_relation M (wf_rep_env domain domain1 input theta) (source_prop_expression wf_rep_raw_body) rawbody ->
  code_relation M (wf_rep_env domain domain1 input theta) (source_prop_expression wf_rep_target_body) targetbody ->
  sf_relation M SFEx rawbody (zeroM M) rawex ->sf_relation M SFEx targetbody (zeroM M) targetex ->
  sf_relation M SFImpl left rawex rawforward ->sf_relation M SFImpl rawex left rawreverse ->
  sf_relation M SFAnd rawforward rawreverse rawpoint ->
  sf_relation M SFImpl left targetex forward ->sf_relation M SFImpl targetex left reverse ->
  sf_relation M SFAnd forward reverse targetpoint ->sf_relation M SFImpl domain targetpoint guardpoint ->
  source_full_prv M b c n rawpoint ->source_full_prv M b c n guardpoint.
Proof.
  intros HB HC HD HL HS HR HT HRaw HTarget HRF HRR HRP HF HRv HP HG PRaw.
  pose proof (source_prop_template_bound M _ wf_rep_target_body (succM M k) HB targetbody HT) as HTB.
  pose proof (proj2 (source_bounded_accept_unary M SFEx targetbody targetex k (or_intror eq_refl) HTarget) HTB) as HTE.
  assert (HFB:source_bounded M forward k).
  { exact (proj2 (source_bounded_accept_binary M SFImpl left targetex forward k
      (or_intror (or_intror eq_refl)) HF) (conj HL HTE)). }
  assert (HRB:source_bounded M reverse k).
  { exact (proj2 (source_bounded_accept_binary M SFImpl targetex left reverse k
      (or_intror (or_intror eq_refl)) HRv) (conj HTE HL)). }
  assert (HPB:source_bounded M targetpoint k).
  { exact (proj2 (source_bounded_accept_binary M SFAnd forward reverse targetpoint k
      (or_introl eq_refl) HP) (conj HFB HRB)). }
  assert (HGB:source_bounded M guardpoint k).
  { exact (proj2 (source_bounded_accept_binary M SFImpl domain targetpoint guardpoint k
      (or_intror (or_intror eq_refl)) HG) (conj HD HPB)). }
  destruct (environment_cons_total M b c n domain) as [d [e [j HConsD]]].
  assert (HCD:context_bounded M d e j k)
    by exact (proj2 (context_bounded_cons M b c n domain d e j k HConsD) (conj HD HC)).
  pose proof (source_full_cons_weaken M b c n domain d e j k rawpoint HConsD HCD PRaw) as PRawD.
  apply (full_source_II M b c n domain targetpoint guardpoint d e j
    (ex_intro _ k (conj HGB HC)));[|exact HConsD|exact HG].
  apply (full_source_CI M d e j forward reverse targetpoint
    (ex_intro _ k (conj HPB HCD)));[| |exact HP].
  - destruct (environment_cons_total M d e j left) as [u [v [l HConsL]]].
    assert (HCL:context_bounded M u v l k)
      by exact (proj2 (context_bounded_cons M d e j left u v l k HConsL) (conj HL HCD)).
    apply (full_source_II M d e j left targetex forward u v l
      (ex_intro _ k (conj HFB HCD)));[|exact HConsL|exact HF].
    apply (source_full_wf_rep_exists_forward M u v l k domain domain1 input theta rawbody targetbody rawex targetex
      HB HCL HR HT HRaw HTarget).
    apply (source_full_modus_ponens M u v l left rawex rawforward HRF).
    + apply (source_full_conjunction_left M u v l rawforward rawreverse rawpoint HRP).
      exact (source_full_cons_weaken M d e j left u v l k rawpoint HConsL HCL PRawD).
    + exact (source_full_cons_head M d e j left u v l k HConsL HL HCL).
  - destruct (environment_cons_total M d e j targetex) as [u [v [l HConsE]]].
    assert (HCE:context_bounded M u v l k)
      by exact (proj2 (context_bounded_cons M d e j targetex u v l k HConsE) (conj HTE HCD)).
    apply (full_source_II M d e j targetex left reverse u v l
      (ex_intro _ k (conj HRB HCD)));[|exact HConsE|exact HRv].
    apply (source_full_modus_ponens M u v l rawex left rawreverse HRR).
    + apply (source_full_conjunction_right M u v l rawforward rawreverse rawpoint HRP).
      exact (source_full_cons_weaken M d e j targetex u v l k rawpoint HConsE HCE PRawD).
    + apply (source_full_wf_rep_exists_reverse M u v l k domain domain1 input theta rawbody targetbody rawex targetex
        HB HCE HS HR HT HRaw HTarget).
      * apply (source_full_cons_weaken M d e j targetex u v l k domain HConsE HCE).
        exact (source_full_cons_head M b c n domain d e j k HConsD HD HCD).
      * exact (source_full_cons_head M d e j targetex u v l k HConsE HTE HCE).
Qed.

Print Assumptions source_full_wf_rep_guarded_point.
