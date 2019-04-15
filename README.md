# LibHyps

This Library provides several coq tactics and tacticals to deal with
hypothesis during a proof.

# Iterator on all hypothesis

- `onAllHyps tac` does `tac H` for each hypothesis `H` of the current goal.
- `onAllHypsRev tac` same as `onAllHyps tac` but in reverse order
  (good for reverting for instance).

# Tacticals to apply on each NEW hypothesis

- `tac1 ;; tac2` applies `tac1` to current goal and then `tac2` to
  each new hypothesis in each subgoal (iteration: newest first).
- `tac1 ;!; tac2` applies `tac1` to current goal and then `tac2` to
  each new hypothesis in each subgoal (older first).

# Cleaning tactics

This tactics are best used in conjunction with the tacticals above.
For instance `tac ;; subst_or_revert` allows to have all new
hypothesis reverted, except the ones that are `subst`able.

- `subst_or_revert H` tries to use `H` to `subst` some variable and
  `revert H` if it fails.
- `move_up_type H` moves `H` to the top of the goal if it is
  Type-Sorted (i.e. not in Prop). This is generally a good heuristic
  to push away non interesting parts of the proof context.

# Specializing a premiss of a hypothesis by its number

- `especialize H at n.` create a subgoal to prove the nth dependent
  hypothesis of `H`, creating necessary evars for non unifiable
  variables. Once proved the subgoal is used to remove the nth
  hypothesis of `H`.

# Customizable hypothesis auto naming system

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

## How to cstomize the naming scheme

Tactic `rename_hyp` should be redefined along a coq development, it
should return a fresh name build from an hypothesis h and its type th.
It should fail if no name is found, so that the fallback scheme is
called.

Typical use, in increasing order of complexity, approximatively
equivalent to the decreasing order of interest.

```
(* Redefining rename_hyp, first define a naming ltac . *)
Ltac rename_hyp_default n th ::=
  let res := 
      match th with
      | (ind1 _ _) => name (`ind1`)
      | (ind1 _ _ ?x ?y) => name (`ind1` ++ x#n ++ y$n)
      | f1 _ ?x = ?y => name (`f1` ++ x#n ++ y#n)
      end in
  res.

    | _ => previously_defined_renaming_tac1 th (* cumulative with previously defined renaming tactics *)
    | _ => previously_defined_renaming_tac2 th
  end.

(* 2 Then overwrite the definition of rename_hyp using the ::= operator. :*)

Ltac rename_hyp ::= my_rename_hyp.
```

## How to define variants of these tacticals?

Some more example of tacticals performing cleaning and renaming on new
hypothesis.

```
(* subst or revert *)
Tactic Notation (at level 4) "??" tactic4(tac1) :=
  (tac1 ;; substHyp ;!; revertHyp).
(* subst or rename or revert *)
Tactic Notation "!!!" tactic3(Tac) := (Tac ;; substHyp ;!; revert_if_norename ;; autorename).
(* subst or rename or revert + move up if in (Set or Type). *)
Tactic Notation (at level 4) "!!!!" tactic4(Tac) :=
      (Tac ;; substHyp ;!; revert_if_norename ;; autorename ;; move_up_types).
```

