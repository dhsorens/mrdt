(* a Coq implementation of MRDTs *)

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Ensembles.
From Coq Require Import Permutation.
From Coq Require Import ZArith_base.
From Coq Require Import QArith_base.
From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Fin.
From Coq.Init Require Import Byte.
From Coq Require Import Lia.

Import ListNotations.
Open Scope N_scope.
Open Scope string.

 (* Definition 3.1 : a sequence of relations is called the characteristic relations of a data type T if for every x y : T, R(x) = R(y) => x = y *)


 (* relational merge specifications *)


 Class mrdt (T : Type) := build_mrdt {
    (* todo *)
    merge : T -> T -> T -> T ;
    (* commutativity, associativity, and idempotence (duplicates not a problem) *)
    merge_comm : forall t t' t'', 
      merge t t' t'' = merge t t'' t' ;
    merge_assoc : forall t t' t'' t''',
      merge t t' (merge t t'' t''') = merge t (merge t t' t'') t''' ;
   (* TODO want this? 
      merge_idem : forall t t' t'',
      t' = t'' -> merge t t' t'' = t' ; *)
 }.



(* Constrcut MRDT from op and diff, e.g. if comm/assoc *)
Definition merge_from_op { T : Type } 
   (op : T -> T -> T) (diff : T -> T -> T) t t' t'' : T := 
   op t (op (diff t' t) (diff t'' t)).

Theorem construct_mrdt (T : Type) : 
   forall (op : T -> T -> T) (diff : T -> T -> T)
      (op_diff  : forall t t', op t (diff t' t) = t')
      (diff_op_assoc : forall t t' t'', diff (op t t') t'' = op t (diff t' t''))
      (* TODO no_conflicts might be provable with diff_op_assoc *)
      (no_conflicts : forall t t' t'', op t' (diff t'' t) = op (diff t' t) t'') 
      (op_comm : forall t t', op t t' = op t' t)
      (op_assoc : forall t t' t'', op t (op t' t'') = op (op t t') t''),
   mrdt T.
Proof.
   intros.
   apply (build_mrdt T (merge_from_op op diff)).
   -  intros.
      unfold merge_from_op.
      now rewrite (op_comm (diff t' t) (diff t'' t)).
   -  intros.
      unfold merge_from_op.
      rewrite (op_assoc t (diff t' t) (diff t'' t)).
      rewrite op_diff.
      rewrite (op_assoc t (diff t'' t) (diff t''' t)).
      rewrite op_diff.
      rewrite (op_assoc t (diff t' t) (diff (op t'' (diff t''' t)) t)).
      rewrite op_diff.
      rewrite (op_assoc t (diff (op t' (diff t'' t)) t) (diff t''' t)).
      rewrite op_diff.
      rewrite <- (op_assoc t' (diff t'' t) (diff t''' t)).
      rewrite (no_conflicts t t'' t''').
      now rewrite diff_op_assoc.
Qed.


(* TODO 
   Types T and P, P is the Patch type; 
   op : T -> P -> T 
   diff : T -> T -> P
   what needed for MRDT?
   *)



(* not true for T == N : (op_diff2  : forall t t', op t' (diff t t') = t) *)


(* TODO
-  Q: diff has to be associative? A: NO. Just in terms of op.
-  Q: idempotence : you need to diff t' t'', if "zero" then "they're equal" and t'
      otherwise do merge
-  notion of inverses (if we don't want to do some poset magic)
*)





(* TODO can I conclude that op is commutative? associative? *)
