(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

Require Export LibHyps.TacNewHyps.
Require Export LibHyps.LibHypsNaming.
(* Require Export LibHyps.LibSpecialize. *)

(* debug *)
Ltac pr_goal :=
  match goal with
    |- ?g =>
      let allh := all_hyps in
      idtac allh " ⊢ " g
  end.

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

(* if T is not already present in cache, return the (cache + (h:T)),
   otherwise return cache unchanged. *)
Ltac find_in_cache_update cache T h :=
  match find_in_cache_T cache T with
    (?c , None) => constr:((DCons T h c , None))
  | (?c , ?res) => constr:((DCons T h c , res))
  end.

(* Precondition: x must be "below" y at start *)
(* equivalent to move x before belowme but fails if x=bleowme. This
   forces the pre-8.14 behaviour of move below. *)
Ltac move_above x y :=
  match constr:((x , y)) with
  | (?c,?c) => idtac
  | _ => move x after y
  end.

(* Precondition: x must be "below" y at start *)
(* equivalent to move x after belowme but fails if x=bleowme *)
Ltac move_below x y :=
  match constr:((x , y)) with
  | (?c,?c) => idtac
  | _ => move x before y
  end.


(* move each hyp in lhyps either after the pivot hyp for its type
found in cache, or just above fstProp if there is no pivot. In this
second case we return a new cache with h as a new pivot. *)
(* Example
There is a number of "segments". A segment for type T is the first set
of consecutive variables of type T, located before the first
Prop-sorted hyp. For sintance there are 2 segments in the goal below,
one is x1-x3 and the other is b1-b2.

  x1 : nat
  x2 : nat
  x3 : nat <-- pivot for nat
  b1 : bool
  b2 : bool <-- pivot for bool
  H : ... : Prop <-- fstProp
  H2: ... : Prop not in lhyps
  x : nat  <-- in lhyps
  b : bool <-- in lhyps
  c : Z    <-- in lhyps
 =======
  ...

This is described by the three arguments:

- cache is (DCons bool b2 (DCons nat x3 DNil)) i.e. last variable of
  each segment 
- lhyps is (DCons nat x (DCons bool b (DCons Z c DNil))) list of
  variable to move (may not contain all the badly place variables)
- fstProp is H.

The goal of group_up_list_ is to move all vars of lhyps to there
segment or above fstProp if there segment does not exist yet.

invariant: the things in lhyps always need to be moved upward,
otherwise move before and move after work the wrong way. *)
Ltac group_up_list_ fstProp cache lhyps :=
  lazymatch lhyps with
  | DCons ?th ?h ?lhyps' =>
    match type of th with
    | Prop => (* lhyps is supposed to be filtered out of Prop already. *)
        idtac "LibHyps: This shoud not happen. Please report.";
        group_up_list_ fstProp cache lhyps'
    | _ =>
      let upd := find_in_cache_update cache th h in
      lazymatch upd with
      | (?newcache , None) => (* there was no pivot for th *)
        match fstProp with
        | @None => idtac (* No Prop Hyp, don't move *)
        | ?hfstprop => move_above h hfstprop
        end;
        group_up_list_ fstProp constr:(DCons th h cache) lhyps'
      | (?newcache , ?theplace) =>
          (* we append h to its segment, and it becomes the new pivot. *)
          (try move_below h theplace);
          group_up_list_ fstProp newcache lhyps'
      end
    end
  | DNil => idtac (* no more hyps to move *)
  end
.

Ltac find_in t lh :=
  match lh with
  | DNil => None
  | (DCons t ?h ?lh') => h
  | (DCons _ ?h ?lh') => find_in t lh'
  end.

(* return a triple for hyps groupinf initiation:
- H: topmost Prop-sorted hyp (where a hyp goes if there is no segment for it).
- list of pivots for each type seen above H (pivot = lowest of the first segment of a type)
- the hypothesis that may need to be moved (not belonging to there first segment).
See group_up_list_ above.
 *)
Ltac build_initial_cache_ acc lh :=
  match acc with
    (?fstProp, ?pivots, ?tomove) =>
      lazymatch lh with
      | DNil => constr:((fstProp, pivots , tomove))
      | (DCons ?th ?h ?lh') =>
          lazymatch type of th with
          | Prop =>
              lazymatch fstProp with (* is this the first Prop? *)
              | @None => build_initial_cache_ (h, pivots, tomove) lh'
              | _ => build_initial_cache_ (fstProp, pivots, tomove) lh'
              end
          | _ => (* Type-sorted hyp *)
              lazymatch fstProp with (* we haven't reached the fstprop *)
              | @None => 
                  (* does this type already have a pivot? if yes don't replace *)
                  let found := find_in th pivots in
                  lazymatch found with
                  | @None => (* no pivot yet, see the next hyp *)
                      lazymatch lh' with
                      | (DCons th _ _) => (* h is correctly placed, not the pivot *)
                          build_initial_cache_ (fstProp, pivots, tomove) lh'
                      | (DCons _ _ _) => (* h is the pivot for th  *)
                          build_initial_cache_ (fstProp, DCons th h pivots , tomove) lh'
                      | DNil => (* h is the pivot for th  *)
                          constr:((fstProp, DCons th h pivots , tomove))
                      end
                  | _ => (* there already is a pivot for th, and it needs to move *)
                      build_initial_cache_ (fstProp, pivots , DCons th h tomove) lh'
                  end
              | _ => (*fstprop already reached, this is not a pivot and needs to move*)
                  build_initial_cache_ (fstProp, pivots , DCons th h tomove) lh'
              end
          end
      end
  end.

Ltac build_initial_cache lh := build_initial_cache_ constr:((@None, DNil, DNil)) lh.

Ltac mem x l :=
  lazymatch l with
  | DNil => false
  | DCons _ x ?l' => true
  | DCons _ _ ?l' => mem x l'
  end.

(* return the intersection of l1 l2 in reverse order of l1 *)
Ltac intersec_ acc l1 l2 :=
  match l1 with
    DNil => acc
  | DCons ?th ?h ?l1' =>
      match (mem h l2) with
      | true => intersec_ (DCons th h acc) l1' l2
      | false => intersec_ acc l1' l2
      end
  end.

Ltac intersec l1 l2 := intersec_ DNil l1 l2.


(* Move up non-Prop hypothesis of lhyps up in the goal, to make Prop
   hyptohesis closer to the conclusion. Also group non-Prop hyps by
   same type to win some place in goal printing.

Note: This tactic takes a list of hyps, you should use the tactical
then_allnh (syntax: ";{! group_up_list }") or then_allnh_rev (syntax:
";{!< group_up_list}"). *)
Ltac group_up_list lhyps :=
  match build_initial_cache all_hyps with
  | (?fstProp, ?cache, ?tomove) =>
      (* tomove is reversed, but intersec re-reverse *)
      let tomove2 := intersec tomove lhyps in
      group_up_list_ fstProp cache tomove2
  end.

(* Stays for compatibility, but for efficiency reason prefer
   rename_all_hyps, which applies on the list of hyptohesis to move.
   Use the corresponding tactical. *)
Ltac move_up_types H :=
  let t := type of H in
  match t with
    Depl => fail "Try to use { } instead of {! }"
  | _ => group_up_list constr:(DCons t H DNil)
  end.


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
