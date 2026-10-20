(** A mixed, stable quotient relation on internally coded environments.
    Literal identity handles markers, padding, and freshly consed names.
    Changed entries require supported deqv codes at every hygienic base. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs NumericalContexts NumericalEnvironments ContextualProofs
  ContextSupport StableContextSupport NumericalEquivalence QuotationPayloads QuotationAtomRebase QuotationHygiene
  SubstitutionEnvironmentTotal.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition quotient_pair_safe M t x y k :=
  coding_lt M (zeroM M) k /\ coding_lt M t k /\ coding_lt M x k /\ coding_lt M y k.
Definition quotient_pair_safe_formula (t x y k : term) : form :=
  Peano.sless zero k ∧ Peano.sless t k ∧ Peano.sless x k ∧ Peano.sless y k.
Lemma quotient_pair_safe_correct M rho t x y k :
  holds M rho (quotient_pair_safe_formula t x y k) <->
  quotient_pair_safe M (evalM M rho t) (evalM M rho x) (evalM M rho y) (evalM M rho k).
Proof.
  unfold quotient_pair_safe_formula,quotient_pair_safe.
  repeat rewrite holds_and. repeat rewrite less_formula_correct. tauto.
Qed.
Lemma quotient_pair_safe_sym M t x y k :
  quotient_pair_safe M t x y k -> quotient_pair_safe M t y x k.
Proof. intros [H0 [Ht [Hx Hy]]]. repeat split;assumption. Qed.
Section SafeBase.
Variable M : Model.
Add Ring quotient_pair_ring : (model_semiring M).
Lemma quotient_pair_safe_total t x y : exists k,quotient_pair_safe M t x y k.
Proof.
  exists (succM M (addM M t (addM M x y))). split;[apply coding_zero_lt_succ|].
  split;[exists (addM M x y);reflexivity|]. split.
  - exists (addM M t y). f_equal. ring.
  - exists (addM M t x). f_equal. ring.
Qed.
End SafeBase.

Definition supported_quotient_pair M tb tc tn t x y :=
  x=y \/ forall k q,quotient_pair_safe M t x y k -> quotation_atom M true x y t k q ->
    stable_context_support M tb tc tn q.
Definition supported_quotient_pair_formula (tb tc tn t x y : term) : form :=
  x == y ∨ ∀∀ (quotient_pair_safe_formula (code_lift2 t) (code_lift2 x) (code_lift2 y) $1 →
    quotation_atom_formula true (code_lift2 x) (code_lift2 y) (code_lift2 t) $1 $0 →
    stable_context_support_formula (code_lift2 tb) (code_lift2 tc) (code_lift2 tn) $0).
Local Opaque holds quotient_pair_safe_formula quotation_atom_formula stable_context_support_formula.
Lemma supported_quotient_pair_correct M rho tb tc tn t x y :
  holds M rho (supported_quotient_pair_formula tb tc tn t x y) <->
  supported_quotient_pair M (evalM M rho tb) (evalM M rho tc) (evalM M rho tn)
    (evalM M rho t) (evalM M rho x) (evalM M rho y).
Proof.
  unfold supported_quotient_pair_formula,supported_quotient_pair.
  rewrite holds_or. repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite quotient_pair_safe_correct. setoid_rewrite quotation_atom_formula_correct.
  setoid_rewrite stable_context_support_formula_correct. setoid_rewrite code_eval_lift2.
  reflexivity.
Qed.
Lemma supported_quotient_pair_definable M tb tc tn t x :
  Definable1 M (supported_quotient_pair M tb tc tn t x).
Proof.
  exists (supported_quotient_pair_formula $5 $4 $3 $2 $1 $0),
    (x .: t .: tn .: tc .: tb .: fun _=>zeroM M).
  intro y. symmetry. apply supported_quotient_pair_correct.
Qed.
Lemma supported_quotient_pair_refl M tb tc tn t x : supported_quotient_pair M tb tc tn t x x.
Proof. now left. Qed.
Lemma supported_quotient_pair_included M tb tc tn td te tm t x y :
  context_included M tb tc tn td te tm -> supported_quotient_pair M tb tc tn t x y ->
  supported_quotient_pair M td te tm t x y.
Proof.
  intros HI [HE|HQ];[now left|right]. intros k q HS HA.
  exact (stable_context_support_included M tb tc tn td te tm q HI (HQ k q HS HA)).
Qed.
Lemma supported_quotient_pair_cons M tb tc tn h td te tm t x y :
  environment_cons M tb tc tn h td te tm -> supported_quotient_pair M tb tc tn t x y ->
  supported_quotient_pair M td te tm t x y.
Proof.
  intros HC [HE|HQ];[now left|right]. intros k q HS HA.
  exact (stable_context_support_cons M tb tc tn h td te tm q HC (HQ k q HS HA)).
Qed.

Lemma supported_quotient_pair_one_base M tb tc tn t x y k q :
  quotient_pair_safe M t x y k -> quotation_atom M true x y t k q ->
  stable_context_support M tb tc tn q -> supported_quotient_pair M tb tc tn t x y.
Proof.
  intros [H0 [Ht [Hx Hy]]] HQ HS. right.
  intros l r [L0 [Lt [Lx Ly]]] HR.
  apply (stable_context_support_equivalent M tb tc tn q r);[|exact HS].
  exact (quotation_atom_rebase M true x y t k l q r H0 L0 Hx Hy Ht Lx Ly Lt HQ HR).
Qed.
Lemma supported_quotient_pair_one_support M tb tc tn t x y k q :
  quotient_pair_safe M t x y k -> quotation_atom M true x y t k q ->
  context_support M tb tc tn q -> supported_quotient_pair M tb tc tn t x y.
Proof.
  intros HK HQ HS. apply (supported_quotient_pair_one_base M tb tc tn t x y k q HK HQ).
  now apply stable_context_support_of_support.
Qed.
Lemma supported_quotient_pair_witness M tb tc tn t x y :
  supported_quotient_pair M tb tc tn t x y ->
  x=y \/ exists k q,quotient_pair_safe M t x y k /\
    quotation_atom M true x y t k q /\ stable_context_support M tb tc tn q.
Proof.
  intros [HE|HS];[now left|right].
  destruct (quotient_pair_safe_total M t x y) as [k HK].
  destruct (quotation_atom_total M true x y t k) as [q HQ].
  exists k,q. split;[exact HK|]. split;[exact HQ|exact (HS k q HK HQ)].
Qed.

(** This is an explicit unproved atom-level interface. It requires stable
    support of each implication xy -> yx; a future KLogic certificate may
    discharge it using a separately stable marker premise. *)
Definition stable_quotient_atom_symmetry M tb tc tn t :=
  forall x y k a b h,quotient_pair_safe M t x y k ->
    quotation_atom M true x y t k a -> quotation_atom M true y x t k b ->
    implication_graph M a b h -> stable_context_support M tb tc tn h.
Lemma stable_quotient_atom_symmetry_included M tb tc tn td te tm t :
  context_included M tb tc tn td te tm -> stable_quotient_atom_symmetry M tb tc tn t ->
  stable_quotient_atom_symmetry M td te tm t.
Proof.
  intros HI HS x y k a b h HK HA HB HH.
  exact (stable_context_support_included M tb tc tn td te tm h HI (HS x y k a b h HK HA HB HH)).
Qed.
Lemma supported_quotient_pair_sym M tb tc tn t x y :
  stable_quotient_atom_symmetry M tb tc tn t ->
  supported_quotient_pair M tb tc tn t x y -> supported_quotient_pair M tb tc tn t y x.
Proof.
  intros HSym [HE|HQ].
  - left. symmetry. exact HE.
  - right. intros k b HS HB.
    pose proof (quotient_pair_safe_sym M t y x k HS) as HS'.
    destruct (quotation_atom_total M true x y t k) as [a HA].
    destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
      (a .: b .: fun _=>zeroM M)) as [h HH].
    exact (stable_context_support_mp M tb tc tn a b h HH
      (HQ k a HS' HA) (HSym x y k a b h HS' HA HB HH)).
Qed.

Lemma stable_quotient_atom_symmetry_from_marker M tb tc tn t marker :
  stable_context_support M tb tc tn marker ->
  (forall x y k a b h,quotient_pair_safe M t x y k ->
    quotation_atom M true x y t k a -> quotation_atom M true y x t k b ->
    implication_graph M a b h -> numerical_implies M marker h) ->
  stable_quotient_atom_symmetry M tb tc tn t.
Proof.
  intros HM HS x y k a b h HK HA HB HH.
  exact (stable_context_support_implies M tb tc tn marker h (HS x y k a b h HK HA HB HH) HM).
Qed.

Definition supported_quotient_environments M b c n d e m bound t tb tc tn :=
  forall i x y,coding_lt M i bound ->
    environment_lookup M b c n i x -> environment_lookup M d e m i y ->
    supported_quotient_pair M tb tc tn t x y.
Definition supported_quotient_environments_formula (b c n d e m bound t tb tc tn : term) : form :=
  ∀∀∀ (Peano.sless $2 (lift3 bound) →
    environment_lookup_formula (lift3 b) (lift3 c) (lift3 n) $2 $1 →
    environment_lookup_formula (lift3 d) (lift3 e) (lift3 m) $2 $0 →
    supported_quotient_pair_formula (lift3 tb) (lift3 tc) (lift3 tn) (lift3 t) $1 $0).
Local Opaque environment_lookup_formula supported_quotient_pair_formula Peano.sless.
Lemma supported_quotient_environments_correct M rho b c n d e m bound t tb tc tn :
  holds M rho (supported_quotient_environments_formula b c n d e m bound t tb tc tn) <->
  supported_quotient_environments M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho d) (evalM M rho e) (evalM M rho m) (evalM M rho bound) (evalM M rho t)
    (evalM M rho tb) (evalM M rho tc) (evalM M rho tn).
Proof.
  unfold supported_quotient_environments_formula,supported_quotient_environments.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite less_formula_correct. setoid_rewrite environment_lookup_formula_correct.
  setoid_rewrite supported_quotient_pair_correct. setoid_rewrite lift3_correct. reflexivity.
Qed.
Lemma supported_quotient_environments_bound_definable M b c n d e m t tb tc tn :
  Definable1 M (fun bound=>supported_quotient_environments M b c n d e m bound t tb tc tn).
Proof.
  exists (supported_quotient_environments_formula $1 $2 $3 $4 $5 $6 $0 $7 $8 $9 $10),
    (b .: c .: n .: d .: e .: m .: t .: tb .: tc .: tn .: fun _=>zeroM M).
  intro bound. symmetry. apply supported_quotient_environments_correct.
Qed.
Lemma supported_quotient_environments_refl M b c n bound t tb tc tn :
  supported_quotient_environments M b c n b c n bound t tb tc tn.
Proof.
  intros i x y Hi HX HY. left. exact (environment_lookup_functional M b c n i x y HX HY).
Qed.
Lemma supported_quotient_environments_zero M b c n d e m t tb tc tn :
  supported_quotient_environments M b c n d e m (zeroM M) t tb tc tn.
Proof. intros i x y Hi. exfalso. exact (coding_not_lt_zero M i Hi). Qed.
Lemma supported_quotient_environments_included M b c n d e m bound t tb tc tn td te tm :
  context_included M tb tc tn td te tm ->
  supported_quotient_environments M b c n d e m bound t tb tc tn ->
  supported_quotient_environments M b c n d e m bound t td te tm.
Proof.
  intros HI HQ i x y Hi HX HY.
  exact (supported_quotient_pair_included M tb tc tn td te tm t x y HI (HQ i x y Hi HX HY)).
Qed.
Lemma supported_quotient_environments_context_cons M b c n d e m bound t tb tc tn h td te tm :
  environment_cons M tb tc tn h td te tm ->
  supported_quotient_environments M b c n d e m bound t tb tc tn ->
  supported_quotient_environments M b c n d e m bound t td te tm.
Proof.
  intros HC HQ i x y Hi HX HY.
  exact (supported_quotient_pair_cons M tb tc tn h td te tm t x y HC (HQ i x y Hi HX HY)).
Qed.
Lemma supported_quotient_environments_sym M b c n d e m bound t tb tc tn :
  stable_quotient_atom_symmetry M tb tc tn t ->
  supported_quotient_environments M b c n d e m bound t tb tc tn ->
  supported_quotient_environments M d e m b c n bound t tb tc tn.
Proof.
  intros HS HQ i y x Hi HY HX.
  exact (supported_quotient_pair_sym M tb tc tn t x y HS (HQ i x y Hi HX HY)).
Qed.

(** The head uses literal equality. No quotient reflexivity, domain fact,
    or freshness premise is needed for this relation-preservation lemma. *)
Theorem supported_quotient_environments_cons M b c n d e m bound t tb tc tn
  head b' c' n' d' e' m' :
  supported_quotient_environments M b c n d e m bound t tb tc tn ->
  environment_cons M b c n head b' c' n' -> environment_cons M d e m head d' e' m' ->
  supported_quotient_environments M b' c' n' d' e' m' (succM M bound) t tb tc tn.
Proof.
  intros HQ HC HD i x y Hi HX HY.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[j ->]].
  - apply (proj1 (environment_cons_head M b c n head b' c' n' x HC)) in HX.
    apply (proj1 (environment_cons_head M d e m head d' e' m' y HD)) in HY.
    left. congruence.
  - apply (HQ j x y).
    + exact (proj1 (coding_lt_succ_cancel M j bound) Hi).
    + exact (proj1 (environment_cons_tail M b c n head b' c' n' j x HC) HX).
    + exact (proj1 (environment_cons_tail M d e m head d' e' m' j y HD) HY).
Qed.
Theorem supported_quotient_environments_cons_context M b c n d e m bound t tb tc tn
  head b' c' n' d' e' m' h td te tm :
  supported_quotient_environments M b c n d e m bound t tb tc tn ->
  environment_cons M b c n head b' c' n' -> environment_cons M d e m head d' e' m' ->
  environment_cons M tb tc tn h td te tm ->
  supported_quotient_environments M b' c' n' d' e' m' (succM M bound) t td te tm.
Proof.
  intros HQ HC HD HT.
  apply (supported_quotient_environments_context_cons M b' c' n' d' e' m'
    (succM M bound) t tb tc tn h td te tm HT).
  exact (supported_quotient_environments_cons M b c n d e m bound t tb tc tn head b' c' n' d' e' m' HQ HC HD).
Qed.

Lemma quotient_pair_safe_from_environments M b c n d e m k t i x y :
  quotation_safe M b c n k t -> quotation_safe M d e m k t ->
  environment_lookup M b c n i x -> environment_lookup M d e m i y ->
  quotient_pair_safe M t x y k.
Proof.
  intros [Ht HL] [Ht' HR] HX HY. split;[exact (environment_below_zero M b c n k HL)|].
  split;[exact Ht|]. split;[exact (HL i x HX)|exact (HR i y HY)].
Qed.
Lemma supported_quotient_lookup_at M b c n d e m bound t tb tc tn k i x y q :
  supported_quotient_environments M b c n d e m bound t tb tc tn ->
  quotation_safe M b c n k t -> quotation_safe M d e m k t ->
  coding_lt M i bound -> environment_lookup M b c n i x -> environment_lookup M d e m i y ->
  quotation_atom M true x y t k q ->
  x=y \/ stable_context_support M tb tc tn q.
Proof.
  intros HE HL HR Hi HX HY HQ. destruct (HE i x y Hi HX HY) as [Hsame|Hpair].
  - now left.
  - right. apply (Hpair k q);[|exact HQ].
    exact (quotient_pair_safe_from_environments M b c n d e m k t i x y HL HR HX HY).
Qed.

Print Assumptions quotient_pair_safe_total.
Print Assumptions supported_quotient_pair_correct.
Print Assumptions supported_quotient_pair_definable.
Print Assumptions supported_quotient_pair_sym.
Print Assumptions supported_quotient_environments_correct.
Print Assumptions supported_quotient_environments_bound_definable.
Print Assumptions supported_quotient_environments_context_cons.
Print Assumptions supported_quotient_environments_sym.
Print Assumptions supported_quotient_environments_cons.
Print Assumptions supported_quotient_environments_cons_context.

Print Assumptions supported_quotient_pair_one_base.
Print Assumptions supported_quotient_pair_witness.
Print Assumptions stable_quotient_atom_symmetry_from_marker.
Print Assumptions supported_quotient_lookup_at.

Print Assumptions supported_quotient_pair_one_support.
Print Assumptions stable_quotient_atom_symmetry_included.
