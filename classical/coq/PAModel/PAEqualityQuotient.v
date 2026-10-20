(** Turn an arbitrary countably enumerated PAeq interpretation into an
    actual project Model whose equality predicate is native equality.
    The full satisfaction theorem includes arbitrary valuations. *)
From Stdlib Require Import Vectors.Vector.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From PAModel Require Import Model CountableCanonicalQuotient PAEqualityRelation
 FullSurjectiveInterpretation.
Import Vector.VectorNotations.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma quotient_vector_zero A (v : Vector.t A 0) : v = ([]).
Proof. apply (Vector.case0 (fun w => w = ([]))). reflexivity. Qed.
Lemma quotient_vector_one A (v : Vector.t A 1) : v = ([Vector.hd v]).
Proof. rewrite (Vector.eta v), (quotient_vector_zero A (Vector.tl v)). reflexivity. Qed.
Lemma quotient_vector_two A (v : Vector.t A 2) :
 v = ([Vector.hd v; Vector.hd (Vector.tl v)]).
Proof. rewrite (Vector.eta v), (quotient_vector_one A (Vector.tl v)). reflexivity. Qed.

Definition pa_quotient_raw D Q (I : interp D) (project : D -> Q) (represent : Q -> D) : interp Q :=
 {| i_func := fun f v => project (@i_func _ _ D I f (Vector.map represent v));
    i_atom := fun _ _ => False |}.

Theorem countable_PAeq_native_model D (I : interp D) (enumerate : nat -> D) :
 (forall x, exists n, enumerate n = x) ->
 (forall phi rho, PAeq phi -> @sat _ _ D I falsity_on rho phi) ->
 exists (M : Model) (project : D -> carrier M) (represent : carrier M -> D),
   (forall x y, pa_equality_relation D I x y <-> project x = project y) /\
   (forall q, project (represent q) = q) /\
   (forall phi rho xi, (forall n, project (rho n) = xi n) ->
      (@sat _ _ D I falsity_on rho phi <-> holds M xi phi)).
Proof.
 intros HEnum HA.
 destruct (paeq_relation_laws D I HA) as (HRefl&HSym&HTrans).
 destruct (paeq_relation_function_laws D I HA) as (HSucc&HAdd&HMult).
 destruct (countable_canonical_quotient D enumerate (pa_equality_relation D I)
   HRefl HSym HTrans HEnum) as (Q&project&represent&HProject&HSection&HRelated).
 set (raw := pa_quotient_raw D Q I project represent).
 set (J := Peano.extensional_model raw).
 assert (HSurj : forall q, exists d, project d = q).
 { intro q. exists (represent q). exact (HSection q). }
 assert (HFunctions : forall f (v : Vector.t D (ar_syms f)),
   project (@i_func _ _ D I f v) = @i_func _ _ Q J f (Vector.map project v)).
 { intros f v. destruct f.
   - rewrite (quotient_vector_zero D v). reflexivity.
   - rewrite (quotient_vector_one D v). cbn.
     apply (proj1 (HProject _ _)). apply HSucc. apply HRelated.
   - rewrite (quotient_vector_two D v). cbn.
     apply (proj1 (HProject _ _)). apply HAdd; apply HRelated.
   - rewrite (quotient_vector_two D v). cbn.
     apply (proj1 (HProject _ _)). apply HMult; apply HRelated. }
 assert (HAtoms : forall p (v : Vector.t D (ar_preds p)),
   @i_atom _ _ D I p v <-> @i_atom _ _ Q J p (Vector.map project v)).
 { intros [] v. rewrite (quotient_vector_two D v). exact (HProject _ _). }
 assert (HTransfer : forall phi rho xi, (forall n, project (rho n) = xi n) ->
   (@sat _ _ D I falsity_on rho phi <-> @sat _ _ Q J falsity_on xi phi)).
 { intros phi rho xi HEnv.
   exact (@full_surjective_satisfaction PA_funcs_signature PA_preds_signature
     D Q I J project HFunctions HAtoms HSurj falsity_on phi rho xi HEnv). }
 assert (HPA : forall phi rho, PAeq phi -> @sat _ _ Q J falsity_on rho phi).
 { intros phi rho Hphi.
   apply (proj1 (HTransfer phi (fun n => represent (rho n)) rho (fun n => HSection (rho n)))).
   exact (HA phi (fun n => represent (rho n)) Hphi). }
 pose (M := Build_Model Q raw HPA).
 exists M, project, represent. split; [exact HProject|].
 split; [exact HSection|]. exact HTransfer.
Qed.

Print Assumptions countable_PAeq_native_model.
