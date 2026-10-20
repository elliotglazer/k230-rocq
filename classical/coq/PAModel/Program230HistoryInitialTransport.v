(** Replace row zero of a coded history while retaining every later row.
    The only semantic premise concerns the first instruction, not a run. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension
 BetaPacking CodeExpressions NumericalProofs Program230Configurations
 Program230Histories Program230HistoryJoin Program230HistoryConstructors.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia setoid_ring.Ring.
Unset Implicit Arguments.

Section InitialTransport.
Variable M:Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Local Notation ten := (code_numeral M 10).
Add Ring history_initial_ring : (model_semiring M).

Definition program230_overlay_relation a b c d cut i value :=
 (coding_lt M i cut /\ beta M a b i value) \/
 (~coding_lt M i cut /\ beta M c d i value).
Definition program230_overlay_formula:form :=
 (Peano.sless $1 $2 ∧ beta_formula $3 $4 $1 $0) ∨
 ((Peano.sless $1 $2 → ⊥) ∧ beta_formula $5 $6 $1 $0).

Lemma program230_overlay_formula_correct rho a b c d cut i value:
 holds M (value.:i.:cut.:a.:b.:c.:d.:rho) program230_overlay_formula <->
 program230_overlay_relation a b c d cut i value.
Proof.
 unfold program230_overlay_formula,program230_overlay_relation.
 rewrite holds_or,!holds_and,holds_imp,!less_formula_correct,!beta_formula_correct.
 reflexivity.
Qed.

Lemma program230_overlay_total a b c d cut i:
 exists value,program230_overlay_relation a b c d cut i value.
Proof.
 destruct (@Peano.trichotomy D (raw_interpretation M)
   (fun ax H rho => axioms M ax rho H) i cut) as [Hlt|[Heq|Hgt]].
 -destruct (beta_total M a b i) as [value Hv];exists value;left;auto.
 -destruct (beta_total M c d i) as [value Hv];exists value;right;split;[|exact Hv].
  intro H;exact (@Peano.lt_neq D (raw_interpretation M)
   (fun ax H rho => axioms M ax rho H) i cut H Heq).
 -destruct (beta_total M c d i) as [value Hv];exists value;right;split;[|exact Hv].
  intro H;pose proof (coding_lt_trans M i cut i H Hgt) as Hii.
  exact (@Peano.lt_neq D (raw_interpretation M)
   (fun ax H rho => axioms M ax rho H) i i Hii eq_refl).
Qed.

Lemma program230_overlay_bound a b c d cut i value:
 program230_overlay_relation a b c d cut i value -> coding_lt M value (S (a+c)).
Proof.
 intros [[_ Hv]|[_ Hv]].
 -eapply coding_le_lt_trans;[exact (remainder_le_dividend M a (beta_modulus M b i) value Hv)|].
  apply coding_le_add.
 -eapply coding_le_lt_trans;[exact (remainder_le_dividend M c (beta_modulus M d i) value Hv)|].
  replace (a+c) with (c+a) by ring;apply coding_le_add.
Qed.

Lemma program230_overlay_unique a b c d cut i value other:
 program230_overlay_relation a b c d cut i value ->
 program230_overlay_relation a b c d cut i other -> value=other.
Proof.
 intros [[Hi Hv]|[Hi Hv]] [[Hj Hw]|[Hj Hw]];try contradiction;
 eapply beta_unique;eassumption.
Qed.

Theorem program230_beta_overlay a b c d cut bound:
 exists f g,forall i value,coding_lt M i bound ->
 (beta M f g i value <-> program230_overlay_relation a b c d cut i value).
Proof.
 set (rho:=cut.:a.:b.:c.:d.:(fun _ => Z)).
 apply (beta_pack_function M rho program230_overlay_formula bound (a+c)).
 -intros i Hi;destruct (program230_overlay_total a b c d cut i) as [value Hv].
  exists value;apply program230_overlay_formula_correct;exact Hv.
 -intros i value Hi Hv;apply program230_overlay_bound with (b:=b)(d:=d)(cut:=cut)(i:=i).
  apply program230_overlay_formula_correct in Hv;exact Hv.
 -intros i value other Hi Hv Hw.
  apply program230_overlay_formula_correct in Hv,Hw.
  exact (program230_overlay_unique a b c d cut i value other Hv Hw).
Qed.

Lemma program230_positive_field_after_zero i j:
 i<>Z -> ~coding_lt M (program230_field_index M i j) ten.
Proof.
 intro Hnz.
 destruct (@Peano.zero_or_succ D (raw_interpretation M)
   (fun ax H rho => axioms M ax rho H) i) as [Hz|[q Hq]].
 -contradiction.
 -rewrite Hq;unfold program230_field_index.
  change (~coding_lt M (ten*S q+code_numeral M j) ten).
  replace (ten*S q+code_numeral M j) with
   (ten+(ten*q+code_numeral M j)) by (rewrite (succ_as_add M q);ring).
  apply coding_not_lt_sum.
Qed.

Theorem program230_history_change_initial step b c N start replacement:
 program230_history M step b c N start ->
 (forall next,program230_step M step start next -> program230_step M step replacement next) ->
 exists f g,
 program230_history M step f g N replacement /\
 (forall i state,coding_lt M i (S N) -> i<>Z ->
  (program230_state_at M b c i state <-> program230_state_at M f g i state)).
Proof.
 intros [Hstart Hrun] Htransfer.
 destruct (program230_state_at_zero_total M replacement) as [a [d Hreplacement]].
 destruct (program230_beta_overlay a d b c ten (ten*S N)) as [f [g Hfg]].
 assert (Hnewstart:program230_state_at M f g Z replacement).
 { intros j Hj;apply (proj2 (Hfg (program230_field_index M Z j)
     (program230_field replacement j)
     (program230_field_index_bound M Z (S N) j Hj (coding_zero_lt_succ M N)))).
   left;split;[rewrite (program230_field_index_zero M j);apply program230_numeral_lt;exact Hj|apply Hreplacement;exact Hj]. }
 assert (Htail:forall i state,coding_lt M i (S N) -> i<>Z ->
    (program230_state_at M b c i state <-> program230_state_at M f g i state)).
 { intros i state Hi Hnz;split;intros Hstate j Hj.
   -apply (proj2 (Hfg (program230_field_index M i j) (program230_field state j)
      (program230_field_index_bound M i (S N) j Hj Hi))).
    right;split;[apply program230_positive_field_after_zero;exact Hnz|apply Hstate;exact Hj].
   -pose proof (proj1 (Hfg (program230_field_index M i j) (program230_field state j)
      (program230_field_index_bound M i (S N) j Hj Hi)) (Hstate j Hj)) as Hvalue.
    destruct Hvalue as [[Hlt _]|[_ HB]];[exfalso;exact (program230_positive_field_after_zero i j Hnz Hlt)|exact HB]. }
 exists f,g;split;[split;[exact Hnewstart|]|exact Htail].
 intros i before after Hi Hbefore Hafter.
 assert (Hafterold:program230_state_at M b c (S i) after).
 { assert (Hbound:coding_lt M (S i) (S N)) by
    (apply (proj2 (coding_lt_succ_cancel M i N));exact Hi).
   assert (Hnz:S i<>Z) by (intro E;apply (zero_ne_succ M i);symmetry;exact E).
   exact (proj2 (Htail (S i) after Hbound Hnz) Hafter). }
 destruct (@Peano.zero_or_succ D (raw_interpretation M)
   (fun ax H rho => axioms M ax rho H) i) as [Hz|[q Hq]].
 -subst i;assert (E:before=replacement) by
    (exact (program230_state_at_functional M f g Z before replacement Hbefore Hnewstart)).
  subst before;apply Htransfer;exact (Hrun Z start after Hi Hstart Hafterold).
 -apply Hrun with (i:=i);[exact Hi| |exact Hafterold].
  assert (Hbound:coding_lt M i (S N)) by
    (exact (coding_lt_trans M i N (S N) Hi (coding_lt_succ M N))).
  assert (Hnz:i<>Z) by
    (rewrite Hq;intro E;apply (zero_ne_succ M q);symmetry;exact E).
  exact (proj2 (Htail i before Hbound Hnz) Hbefore).
Qed.

Corollary program230_history_change_initial_endpoint step b c N start replacement last:
 program230_history M step b c N start -> N<>Z ->
 program230_state_at M b c N last ->
 (forall next,program230_step M step start next -> program230_step M step replacement next) ->
 exists f g,
 program230_history M step f g N replacement /\
 program230_state_at M f g N last /\
 (forall i state,coding_lt M i (S N) -> i<>Z ->
  (program230_state_at M b c i state <-> program230_state_at M f g i state)).
Proof.
 intros Hrun Hnz Hlast Hstep.
 destruct (program230_history_change_initial step b c N start replacement Hrun Hstep)
  as [f [g [HR HT]]].
 exists f,g;split;[exact HR|split;[|exact HT]].
 exact (proj1 (HT N last (coding_lt_succ M N) Hnz) Hlast).
Qed.

End InitialTransport.
Print Assumptions program230_beta_overlay.
Print Assumptions program230_history_change_initial.
Print Assumptions program230_history_change_initial_endpoint.
