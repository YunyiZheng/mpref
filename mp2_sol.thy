(* < *)
theory mp2_sol
  imports Main
begin
(* > *)
section{*Boolean Expressions, Evaluation and Substitution*}

text{*
The following is a slightly revised version of the type of boolean
expressions presented in class.
*}
datatype 'a boolexp =
   TRUE | FALSE |Atom 'a | Not "'a boolexp"
  | And "'a boolexp" "'a boolexp"
  | Or "'a boolexp" "'a boolexp"
  | Implies "'a boolexp" "'a boolexp"

text{* And the following is an implementation of the Standard
Interpretation function defined on page 4 0f
\texttt{02\_prop\_log\_model.pdf}. *}

fun boolexp_eval 
where
   "boolexp_eval v TRUE = True"
 | "boolexp_eval v FALSE = False"
 | "boolexp_eval v (Atom x) = v x"
 | "boolexp_eval v (Not b) = (\<not> (boolexp_eval v b))"
 | "boolexp_eval v (And a b) =
    ((boolexp_eval v a) \<and> (boolexp_eval v b))"
 | "boolexp_eval v (Or a b) =
    ((boolexp_eval v a) \<or> (boolexp_eval v b))"
 | "boolexp_eval v (Implies a b) =
    ((\<not> (boolexp_eval v a))\<or> (boolexp_eval v b))"

section{* Problems *}

text{*
Below you are asked to define substitution and the set of variables
occurring in a proposition.  You are additionally asked to prove a few
simple properties about these two functions.

\begin{problem} (7 pts)
Define @{term "boolexp_subst"} that, given a propositional atom (@{term "x :: 'a"}), and two
boolexps, creates a third boolexp that is the result of replacing all
occurrences of the propositional atom in the second boolexp with the first
boolexp.

You will likely find it helpful to use something like
@{term "(if x = y then result1 else result2)"}
\end{problem}
*}
fun boolexp_subst :: "'a \<Rightarrow> 'a boolexp \<Rightarrow> 'a boolexp \<Rightarrow> 'a boolexp" where
  "boolexp_subst x b TRUE = TRUE"
| "boolexp_subst x b FALSE = FALSE"
| "boolexp_subst x b (Atom y) = (if x = y then b else (Atom y))"
| "boolexp_subst x b (Not b1) = Not (boolexp_subst x b b1)"
| "boolexp_subst x b (And b1 b2) = And (boolexp_subst x b b1) (boolexp_subst x b b2)"
| "boolexp_subst x b (Or b1 b2) = Or (boolexp_subst x b b1) (boolexp_subst x b b2)"
| "boolexp_subst x b (Implies b1 b2) = Implies (boolexp_subst x b b1) (boolexp_subst x b b2)"

text{* If you have done your work right, the following should give a result of
@{term "And (Atom ''b'') (Implies (Atom ''b'') TRUE) :: char list boolexp"}
*}

value "boolexp_subst ''a'' (Implies (Atom ''b'') TRUE) (And (Atom ''b'') (Atom ''a''))"

text{*
\begin{problem} (3 pts)
Prove that if you evaluate with a valuation @{term "v"} a boolexp that is the
result of substituting all occurences of a propositional atom @{term "x"} by
the proposition @{const "TRUE"}, the result is the same as if you had evaluated the
original boolexp using the valuation @{term "(\<lambda> y. if y = x then TRUE else v y)"}
\end{problem}
*}

lemma subst_to_eval: 
"boolexp_eval v (boolexp_subst x TRUE b) = 
 boolexp_eval (\<lambda> y. if y = x then True else v y) b"
  by (induct "b", simp_all)

text{*
\begin{problem} (6 pts)
Define a function @{term "atoms_of_boolexp :: 'a boolexp \<Rightarrow>
'a list"} that returns a list containing exactly the propositional
atoms that occur in the input boolexp.  Duplicates are allowed in the
list.  There is no required order.  The empty list is represented by
@{term "[]"}.  To insert an element @{term "x"} at the front of a list
@{term "lst"} use @{term "(x # lst)"}.  To append list @{term "l2"}
onto list @{term "l1"} use @{term "(l1 @ l2)"}.
\end{problem}
*}

fun  atoms_of_boolexp :: "'a boolexp \<Rightarrow> 'a list" where
  "atoms_of_boolexp TRUE = []"
| "atoms_of_boolexp FALSE = []"
| "atoms_of_boolexp (Atom x) = [x]"
| "atoms_of_boolexp (Not b) = atoms_of_boolexp b"
| "atoms_of_boolexp (And b1 b2) = (atoms_of_boolexp b1) @ (atoms_of_boolexp b2)"
| "atoms_of_boolexp (Or b1 b2) = (atoms_of_boolexp b1) @ (atoms_of_boolexp b2)"
| "atoms_of_boolexp (Implies b1 b2) = (atoms_of_boolexp b1) @ (atoms_of_boolexp b2)"

text{*
If your definition in Problem 3 is correct, the following lemma should
complete, producing a theorem
*}

lemma test_problem3:
"set (atoms_of_boolexp (Or (Implies (Atom ''b'') TRUE) (And (Atom ''b'') (Atom ''a'')))) =
 {''a'', ''b''}"
by (simp, blast)

text{*
\begin{problem} (3 pts)
Prove that if two valuations are the same on the propositional atoms in a
boolexp, then they will give the same result when used to evaluate the boolexp.
*}

lemma same_on_atoms_same_value:
"(\<forall> x. x : set (atoms_of_boolexp b) \<longrightarrow> v1 x = v2 x) \<longrightarrow>
  (boolexp_eval v1 b = boolexp_eval v2 b)"
by (induct b, simp_all)

text{*
\begin{problem} (3 pts)
Prove that substituting for an atom that is not in a boolexp yields
the same boolexp.
*}

lemma subst_nonexistant_atom:
"x \<notin> set(atoms_of_boolexp b) \<longrightarrow> (boolexp_subst x b' b = b)"
by (induct "b", simp_all)


end
