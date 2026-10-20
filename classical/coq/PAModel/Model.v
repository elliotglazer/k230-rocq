(** Actual PA models. No soundness invariant or unrestricted induction is
    included among the assumptions. Equality is interpreted as equality on
    the carrier. A later completeness adapter will handle equality predicates. *)
From Stdlib Require Import Logic.Classical_Prop Logic.ClassicalChoice Vectors.Vector.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Import Vector.VectorNotations.
Unset Implicit Arguments.

Record Model : Type := {
  carrier : Type;
  raw_interpretation : interp carrier;
  axioms : forall phi rho, PAeq phi ->
    @sat PA_funcs_signature PA_preds_signature carrier
      (Peano.extensional_model raw_interpretation) falsity_on rho phi
}.
Arguments axioms _ _ _ _ : clear implicits.

Definition interpretation (M : Model) : interp (carrier M) :=
  Peano.extensional_model (raw_interpretation M).

Definition holds (M : Model) (rho : nat -> carrier M) (phi : form) : Prop :=
  @sat PA_funcs_signature PA_preds_signature (carrier M)
    (interpretation M) falsity_on rho phi.
Arguments holds M rho phi : clear implicits.

Definition zeroM (M : Model) : carrier M :=
  @i_func _ _ (carrier M) (interpretation M) Zero ([]).
Definition succM (M : Model) (x : carrier M) : carrier M :=
  @i_func _ _ (carrier M) (interpretation M) Succ ([x]).
Definition addM (M : Model) (x y : carrier M) : carrier M :=
  @i_func _ _ (carrier M) (interpretation M) Plus ([x;y]).
Definition mulM (M : Model) (x y : carrier M) : carrier M :=
  @i_func _ _ (carrier M) (interpretation M) Mult ([x;y]).
Arguments succM M x : clear implicits.
Arguments addM M x y : clear implicits.
Arguments mulM M x y : clear implicits.

(** An ordinary formula with one distinguished variable and fixed parameters.
    The parameters may themselves be nonstandard elements of M. *)
Definition Definable1 (M : Model) (P : carrier M -> Prop) : Prop :=
  exists phi rho, forall x, P x <-> holds M (x .: rho) phi.

Lemma definable_induction (M : Model) (P : carrier M -> Prop) :
  Definable1 M P -> P (zeroM M) ->
  (forall x, P x -> P (succM M x)) -> forall x, P x.
Proof.
  intros [phi [rho HP]] H0 HS x.
  pose proof (axioms M (ax_induction phi) rho (PAeq_induction phi)) as HI.
  cbn in HI.
  apply (proj2 (HP x)).
  apply HI.
  - rewrite sat_comp.
    eapply sat_ext; [|exact (proj1 (HP _) H0)].
    intros [|n]; reflexivity.
  - intros y Hy. rewrite sat_comp.
    eapply sat_ext; [|exact (proj1 (HP _) (HS y (proj2 (HP y) Hy)))].
    intros [|n]; reflexivity.
Qed.

Lemma zero_ne_succ (M : Model) (x : carrier M) :
  zeroM M <> succM M x.
Proof.
  exact (@Peano.zero_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x).
Qed.

Lemma succ_injective (M : Model) (x y : carrier M) :
  succM M x = succM M y -> x = y.
Proof.
  exact (@Peano.succ_inj (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) y x).
Qed.
