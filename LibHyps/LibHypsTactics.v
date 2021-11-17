(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

Require Export LibHyps.TacNewHyps.
Require Export LibHyps.LibHypsNaming.
Require Export LibHyps.LibSpecialize.

(* debug *)
(*
Ltac pr_goal :=
  match goal with
    |- ?g =>
      let allh := all_hyps in
      idtac allh " ⊢ " g
  end.*)

(* Default behaviour: generalize hypothesis that we failed to rename,
   so that no automatic names are introduced by mistake. Of course one
   can do "intros" to reintroduce them.

   Revert needs to be done in the other direction (so better do ";;
   autorename ;!; revertHyp"), and may fail if something depends on
   the reverted hyp. So we should revert everything depending on the
   unrenamed hyp. *)
Ltac revert_if_norename H :=
  let t := type of H in
  match type of t with
  | Prop => match goal with
            | _ =>  let x := fallback_rename_hyp_name t in idtac
            (* since we are only in prop it is almost never the case
               that something depends on H but if this happens we revert
               everything that does. This needs testing. *)
            | _ => try revert dependent H
            end
  | _ => idtac
  end.

Ltac rename_or_revert H := autorename_strict H + revert H.

(* Some usual tactics one may want to use with onNewHypsOf: *)
(* apply subst using H if possible. *)
(*Ltac substHyp H :=
  match type of H with
  | ?x = ?y => move H at top; (* to ensure subst will take this hyp *)
               once (subst x + subst y)
  end. *)

(* This is similar to subst x, but ensures that H and only H is used.
   Even if there is another hyp with the same variable *)
Ltac substHyp H :=
  match type of H with
  | Depl => fail 1 (* fail immediately, we are applying on a list of hyps. *)
  | ?x = ?y =>
    (* subst would maybe subst using another hyp, so use replace to be sure *)
    once ((is_var(x); replace x with y in *; [try clear x ; try clear H] )
          + (is_var(y); replace y with x in * ; [try clear y; try clear H]))
  | _ => idtac
  end.

(* revert, fails if impossible, should not fail if hyps are ordered in the right order *)
Ltac revertHyp H := revert H. (* revert is a tactic notation, so we need to define this *)

(* revert if subst fails. Never fail, be careful not to use this tactic in the
   left member of a "+" tactical: *)
Ltac subst_or_revert H := try first [progress substHyp H | revert H].

(* try subst. Never fail, be careful to not use this tactic in the
   left member of a "+" tactical: *)
Ltac subst_or_idtac H := substHyp H.

Ltac map_tac tac lH :=
  lazymatch lH with
    (DCons _ ?Hyp ?lH') => (try tac Hyp); map_tac tac lH'
  | DNil => idtac
  end.

(* Naive variants for lists of hyps. We might want to optimize if
   possible like group_up_list. *)
Ltac subst_or_revert_l := map_tac subst_or_revert.
Ltac subst_or_idtac_l := map_tac subst_or_idtac.
Ltac revertHyp_l := map_tac revertHyp.
Ltac substHyp_l := map_tac ltac:(fun x => try substHyp x) substHyp.
Ltac revert_if_norename_l := map_tac revert_if_norename.
Ltac autorename_l := map_tac autorename.

(* Auto rename all hypothesis *)
Ltac rename_all_hyps := autorename_l  all_hyps.



(* return the lowest hyp with type T in segment lH. We suppose lH is
given lower-first. I.e. we return the first hyp of type T. *)
Ltac find_lowest_T T candidate lH :=
  lazymatch lH with
  | (DCons T ?Hyp _) => Hyp
  | (DCons _ ?Hyp ?lH') => find_lowest_T T candidate lH'
  | _ => candidate
  end.

(* Look into the cache for a hyp of type T. If found, returns the hyp
   + the cache where hyp is deleted. *)
Ltac find_in_cache_T cache T :=
  lazymatch cache with
  | DCons ?th ?h ?cache' =>
    match th with
      | T => constr:((cache' , h))
      | _ =>
        let recres := find_in_cache_T cache' T in
        match recres with
        | (_,@None T) => constr:((cache,@None T))
        | (?newcache1,?res1) => constr:((DCons th h newcache1 , res1))
        end
    end
  | _ => constr:((cache,@None T))
  end.

Ltac find_in_cache_update cache T h :=
  match find_in_cache_T cache T with
    (?c , ?res) => constr:((DCons T h c , res))
  end.



(* Finds the topest Prop-srted hyp. If none found, return candidate. *)
Ltac find_topest_prop others lH :=
  lazymatch lH with
  | (?hs' ?Hyp) =>
    let THyp := type of Hyp in
    match type of THyp with
    | Prop => find_topest_prop hs' hs'
    | Type => find_topest_prop others hs'
    | Set => find_topest_prop others hs'
    end
  | _ => others
  end.

(* equivalent to move x before belowme but fails if x=bleowme. This
   forces the pre-8.14 behaviour of move below. *)
Ltac move_below x belowme :=
  match constr:((x , belowme)) with
  | (?c,?c) => idtac
  | _ => move x before belowme
  end.

(* equivalent to move x after belowme but fails if x=bleowme *)
Ltac move_above x aboveme :=
  match constr:((x , aboveme)) with
  | (?c,?c) => idtac
  | _ => move x after aboveme
  end.

Local Tactic Notation "move" hyp(x) "below" hyp(y)
  := (move_below x y).
Local Tactic Notation "move" hyp(x) "above" hyp(y)
  := (move_above x y).

Ltac group_up_list_ fstProp cache lhyps :=
  lazymatch lhyps with
  | DCons ?th ?h ?lhyps' =>
    match type of th with
    | Prop => group_up_list_ fstProp cache lhyps'
    | _ => 
      let upd := find_in_cache_update cache th h in
      lazymatch upd with
      | (?newcache , None) =>
        match fstProp with
        | @None => idtac (* No Prop Hyp, don't move *)
        | ?hfstprop => move h above hfstprop
        end;
        group_up_list_ fstProp constr:(DCons th h cache) lhyps'
      | (?newcache , ?theplace) =>
          (try move h below theplace); group_up_list_ fstProp newcache lhyps'
      end
    end
  | _ => idtac
  end
.



Ltac find_in t lh :=
  match lh with
  | DNil => None
  | (DCons t ?h ?lh') => h
  | (DCons _ ?h ?lh') => find_in t lh'
  end.

Ltac build_initial_cache_ lh :=
  lazymatch lh with
  | DNil => constr:((@None , DNil))
  | (DCons ?th ?h ?lh') =>
    lazymatch type of th with
    | Prop => constr:((h, DNil)) (* Adding the topest Prop *)
    | _ =>
      let recres := build_initial_cache_ lh' in
      match recres with
      | (?fstProp , ?rescache) => 
        let found := find_in th rescache in
        lazymatch found with
        | @None => constr:((fstProp, DCons th h rescache))
        | _ =>
          match lh' with
          | (DCons th _ _) => recres
          | (DCons _ _ _) => constr:((fstProp, DCons th h rescache))
          | DNil => fail 0 (* assert false, found above would be None *)
          end
        end
      end
    end
  end.

(* the cache is a pair: (H:first Prop-sorted hyp, list of each
   variable that is above H and the last of its type segment). *)
Ltac build_initial_cache lh := build_initial_cache_ lh.


(* Move up non-Prop hypothesis of lhyps up in the goal, to make Prop
   hyptohesis closer to the conclusion. Also group non-Prop hyps by
   same type to win some place in goal printing.

Note: This tactic takes a list of hyps, you should use the tactical
then_allnh (syntax: ";{! group_up_list }") or then_allnh_rev (syntax:
";{!< group_up_list}"). *)
Ltac group_up_list lhyps :=
  match build_initial_cache all_hyps with
  | (?fstProp, ?cache) => group_up_list_ fstProp cache lhyps
  end.

(* Stays for compatibility, but for efficiency reason prefer
   rename_all_hyps, which applies on the list of hyptohesis to move.
   Use the corresponding tactical. *)
Ltac move_up_types H :=
  let t := type of H in
  group_up_list constr:(DCons t H DNil).


(* 
(* Tests *)
Export TacNewHyps.Notations.
Goal forall x1 x3:bool, forall a z e : nat,
      z+e = a
      -> forall SEP:(True -> True),
        a = z+z
        -> ((fun f => z = e) true)
        -> forall b1 b2 b3 b4: bool,
          True -> True.
Proof.
  (* Set Ltac Debug. *)
  (* then_nh_rev ltac:(intros) ltac:(subst_or_idtac).   *)
  intros ; {! group_up_list }.
  (* intros ? ? ? ? ? ? ? ? ? ?. *)
  (* group_up_list (DCons bool b1 DNil). *)
  Undo.
  intros ; { move_up_types }.
  Undo.
  intros ; { autorename }; {! group_up_list }.
  Undo.
  intros ; {subst_or_idtac} ; { autorename } ; {! group_up_list }.
  Undo.
  Fail progress intros ; { revertHyp }.
  intros.
  let hyps := all_hyps in
  idtac hyps.
  Undo 2.
  then_eachnh ltac:(intros) ltac:(subst_or_idtac).  
  Undo.
  Fail intros ; { fun h => autorename_strict h }.
  intros ; { fun h => idtac h }.
  intros ; { ltac:(fun h => idtac h) }.
*)
