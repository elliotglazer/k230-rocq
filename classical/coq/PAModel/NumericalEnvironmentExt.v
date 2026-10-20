(** Equality of the total zero-extended functions represented by internally
    finite environments. The two lengths need not be equal. *)
From PAModel Require Import Model FiniteCoding NumericalEnvironments.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition environment_equivalent_formula (b c n d e m : term) : form :=
  ∀∀ ((environment_lookup_formula (environment_lift2 b) (environment_lift2 c)
        (environment_lift2 n) $1 $0 →
       environment_lookup_formula (environment_lift2 d) (environment_lift2 e)
        (environment_lift2 m) $1 $0) ∧
      (environment_lookup_formula (environment_lift2 d) (environment_lift2 e)
        (environment_lift2 m) $1 $0 →
       environment_lookup_formula (environment_lift2 b) (environment_lift2 c)
        (environment_lift2 n) $1 $0)).

Theorem environment_equivalent_formula_correct (M : Model) rho b c n d e m :
  holds M rho (environment_equivalent_formula b c n d e m) <->
  environment_equivalent M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho d) (evalM M rho e) (evalM M rho m).
Proof.
  unfold environment_equivalent_formula,environment_equivalent.
  match goal with |- _ <-> ?rhs =>
    change ((forall i v,
      (holds M (v .: i .: rho)
        (environment_lookup_formula (environment_lift2 b) (environment_lift2 c)
          (environment_lift2 n) $1 $0) ->
       holds M (v .: i .: rho)
        (environment_lookup_formula (environment_lift2 d) (environment_lift2 e)
          (environment_lift2 m) $1 $0)) /\
      (holds M (v .: i .: rho)
        (environment_lookup_formula (environment_lift2 d) (environment_lift2 e)
          (environment_lift2 m) $1 $0) ->
       holds M (v .: i .: rho)
        (environment_lookup_formula (environment_lift2 b) (environment_lift2 c)
          (environment_lift2 n) $1 $0))) <-> rhs)
  end.
  setoid_rewrite environment_lookup_formula_correct.
  setoid_rewrite environment_eval_lift2. reflexivity.
Qed.

Theorem environment_equivalent_refl (M : Model) b c n :
  environment_equivalent M b c n b c n.
Proof. intros i v. reflexivity. Qed.

Theorem environment_equivalent_sym (M : Model) b c n d e m :
  environment_equivalent M b c n d e m -> environment_equivalent M d e m b c n.
Proof. intros H i v. symmetry. apply H. Qed.

Theorem environment_equivalent_trans (M : Model) b c n d e m f g k :
  environment_equivalent M b c n d e m ->
  environment_equivalent M d e m f g k ->
  environment_equivalent M b c n f g k.
Proof. intros H H' i v. transitivity (environment_lookup M d e m i v); auto. Qed.

Theorem environment_equivalent_lookup (M : Model) b c n d e m i v :
  environment_equivalent M b c n d e m ->
  environment_lookup M b c n i v -> environment_lookup M d e m i v.
Proof. intros H Hv. now apply H. Qed.

Theorem environment_equivalent_lookup_determinacy (M : Model) b c n d e m i v w :
  environment_equivalent M b c n d e m ->
  environment_lookup M b c n i v -> environment_lookup M d e m i w -> v=w.
Proof.
  intros H Hv Hw. apply (environment_lookup_functional M d e m i v w); [|exact Hw].
  now apply H.
Qed.

(** A direct pointwise characterization is useful when a proof already
    provides results from each environment without a common lookup value. *)
Theorem environment_equivalent_iff_lookup_determinacy
    (M : Model) b c n d e m :
  environment_equivalent M b c n d e m <->
  (forall i v w, environment_lookup M b c n i v ->
    environment_lookup M d e m i w -> v=w).
Proof.
  split.
  - intros H i v w. exact (environment_equivalent_lookup_determinacy M b c n d e m i v w H).
  - intros H i v. split; intro Hv.
    + destruct (environment_lookup_total M d e m i) as [w Hw].
      specialize (H i v w Hv Hw). now subst w.
    + destruct (environment_lookup_total M b c n i) as [w Hw].
      specialize (H i w v Hw Hv). now subst w.
Qed.

(** All parameter positions may depend on the induction variable through
    arbitrary arithmetic terms. This does not require any length equality. *)
Theorem environment_equivalent_terms_definable (M : Model) rho b c n d e m :
  Definable1 M (fun x =>
    environment_equivalent M
      (evalM M (x .: rho) b) (evalM M (x .: rho) c) (evalM M (x .: rho) n)
      (evalM M (x .: rho) d) (evalM M (x .: rho) e) (evalM M (x .: rho) m)).
Proof.
  exists (environment_equivalent_formula b c n d e m),rho.
  intro x. symmetry. apply environment_equivalent_formula_correct.
Qed.

Theorem environment_equivalent_definable (M : Model) b c n d e :
  Definable1 M (fun m => environment_equivalent M b c n d e m).
Proof.
  exists (environment_equivalent_formula $5 $4 $3 $2 $1 $0),
    (e .: d .: n .: c .: b .: fun _ => zeroM M).
  intro m. symmetry. apply environment_equivalent_formula_correct.
Qed.

(** Two environments with different lengths are equivalent whenever every
    entry of both represented functions is zero. *)
Theorem environment_zero_equivalent (M : Model) b c n d e m :
  (forall i v, coding_lt M i n -> beta M b c i v -> v=zeroM M) ->
  (forall i v, coding_lt M i m -> beta M d e i v -> v=zeroM M) ->
  environment_equivalent M b c n d e m.
Proof.
  intros H H'. apply environment_equivalent_iff_lookup_determinacy.
  intros i v w [[Hi Hv]|[Hi Hv]] [[Hj Hw]|[Hj Hw]].
  - rewrite (H i v Hi Hv), (H' i w Hj Hw). reflexivity.
  - rewrite (H i v Hi Hv). symmetry. exact Hw.
  - rewrite (H' i w Hj Hw). exact Hv.
  - congruence.
Qed.
