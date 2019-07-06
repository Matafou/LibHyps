This Library provides several coq tactics and tacticals to deal with
hypothesis during a proof.

Main page and documentation: https://github.com/Matafou/LibHyps

## Quick install using opam

```bash
opam install coq-libhyps
```

## Quick install using github:

Clone the github repository:

```bash
git clone https://github.com/Matafou/LibHyps
```
then compile:
```bash
configure.sh
make
make install
```

## Quick test:

```coq
Require Import LibHyps.LibHyps.
```
Demo file [LibHypsDemo.v](https://github.com/Matafou/LibHyps/blob/master/LibHyps/LibHypsDemo.v).

## Short description:

Among manipulations on hypothesis we provide:

- Automatically give better names to hypothesis. The name is computed from the type of the hypothesis so that it resists lots of script changes.
- specialize the nth premis of a hypothesis (forward reasoning without copy-paste).
- move up non-prop hypothesis, to focus on properties
- apply subst on the fly.
- ...

These manipulations can be applied:
- to one hyp
- to all hyps
- to "new" hyps after some tactics.


### Example

```coq
Lemma foo: forall x y z:nat,
    x = y -> forall  a b t : nat, a+1 = t+2 -> b + 5 = t - 7 ->  (forall u v, v+1 = 1 -> u+1 = 1 -> a+1 = z+2)  -> z = b + x-> True.
Proof.
  intros.
  (* ugly names *)
  Undo.
  intros ;; autorename. (* ;; here means "apply to all new hyps" *)
  (* better names *)
  Undo.
  (* short syntax: *)
  !intros.
  Undo.
  (* same thing but use subst if possible, and push non prop hyps to the top. *)
  intros;; substHyp;; autorename;;move_up_types.
  Undo.
  (* short syntax: *)  
  !!!intros.
  (* Let us instantiate the 2nd premis of h_all_eq_add_add without copying its type: *)
  especialize h_all_eq_add_add at 2.
  { apply Nat.add_0_l. }
  (* now h_all_eq_add_add is specialized *)

  Undo 6.
  intros until 1.
  (** Do subst on new hyps only, notice how x=y is not subst and
    remains as 0 = y. Contrary to z = b  + x which is substituted. *)
  (destruct x eqn:heq;intros);; substHyp.
  - apply I.
  - apply I.
Qed.
```

A short description of the features follows.

### Iterator on all hypothesis

- `onAllHyps tac` does `tac H` for each hypothesis `H` of the current goal.
- `onAllHypsRev tac` same as `onAllHyps tac` but in reverse order
  (good for reverting for instance).

### Tacticals to apply on each NEW hypothesis

- `tac1 ;; tac2` applies `tac1` to current goal and then `tac2` to
  each new hypothesis in each subgoal (iteration: newest first).
- `tac1 ;!; tac2` applies `tac1` to current goal and then `tac2` to
  each new hypothesis in each subgoal (older first).

### Cleaning tactics

This tactics are best used in conjunction with the tacticals above.
For instance `tac ;; subst_or_revert` allows to have all new
hypothesis reverted, except the ones that are `subst`able.

- `subst_or_revert H` tries to use `H` to `subst` some variable and
  `revert H` if it fails.
- `move_up_type H` moves `H` to the top of the goal if it is
  Type-Sorted (i.e. not in Prop). This is generally a good heuristic
  to push away non interesting parts of the proof context.

### Specializing a premiss of a hypothesis by its number

- `especialize H at n.` create a subgoal to prove the nth dependent
  hypothesis of `H`, creating necessary evars for non unifiable
  variables. Once proved the subgoal is used to remove the nth
  hypothesis of `H`.

### Customizable hypothesis auto naming system

Using previous taticals (in particular the `;!;` tactical), some
tactic allow to rename hypothesis automatically.

- `autorename H` rename `H` according to the current naming scheme
  (which is customizable, see below).

- `rename_all_hyps` applies `autorename` to all hypothesis.

- `!tac` applies tactic `tac` and then applies autorename to each new
  hypothesis. Shortcut for: `(Tac ;!; revert_if_norename ;;
  autorename).`.`

- `!!tac` same as `!tac` with lesser priority (less than `;`) to apply
  renaming after a group of chained tactics.

#### How to cstomize the naming scheme

The naming engine analyzes the type of hypothesis and generates a name
mimicking the first levels of term structure. At each level the
customizable tactic `rename_hyp` is called. One can redefine it at
will. It must be of the following form:

```coq
(** Redefining rename_hyp*)
(* First define a naming ltac. It takes the current level n and
   the sub-term th being looked at. It returns a "name". *)
Ltac rename_hyp_default n th ::=
   match th with
   | (ind1 _ _) => name (`ind1`)
   | (ind1 _ _ ?x ?y) => name (`ind1` ++ x#(S n)x ++ y$n)
   | f1 _ ?x = ?y => name (`f1` ++ x#n ++ y#n)
   | _ => previously_defined_renaming_tac1 n th (* cumulative with previously defined renaming tactics *)
   | _ => previously_defined_renaming_tac2 n th
   end.

(* Then overwrite the definition of rename_hyp using the ::= operator. :*)
Ltac rename_hyp ::= my_rename_hyp.
```

Where:

- `` `id` `` to use the name id itself
- `t$n` to recursively call the naming engine on term t, n being the maximum depth allowed
- `name ++ name` to concatenate name parts.


#### How to define variants of these tacticals?

Some more example of tacticals performing cleaning and renaming on new
hypothesis.

```coq
(* subst or revert *)
Tactic Notation (at level 4) "??" tactic4(tac1) :=
  (tac1 ;; substHyp ;!; revertHyp).
(* subst or rename or revert *)
Tactic Notation "!!!" tactic3(Tac) := (Tac ;; substHyp ;!; revert_if_norename ;; autorename).
(* subst or rename or revert + move up if in (Set or Type). *)
Tactic Notation (at level 4) "!!!!" tactic4(Tac) :=
      (Tac ;; substHyp ;!; revert_if_norename ;; autorename ;; move_up_types).
```

