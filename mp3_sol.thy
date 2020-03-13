(*<*)
theory mp3_sol
imports Hoare_ann_SIMP lifted_int_data
begin
(*>*)

section{*Problems*}
text{* The problems below are designed to step you through some of the
pieces of reasoning about Hoare Logic proofs in Isabelle.  The first set
give you practice using a combination of ``lifted'' rules and facts from
propositional logic, and the definitions of ``lifted'' operators to
reduce the problem to tractable problems in basic HOL.  The second set
extend this exercise to reasoning about ``lifted'' arithmetic facts, and
the third set ask you to prove certain Hoare triples.
*}

subsection{*Lifted Propositional Logic*}
text{*
In the first three problems below you will prove the ``lifted'' versions of
three problems from  MP1.  You are free to use any and all theorem
proving methods in Isabelle to prove them.  You may wish to refer to the
definitions and theorems in \texttt{lifted\_basic} and 
\texttt{lifted\_predicate\_logic}.  For an example, here is the
``lifted'' version of the first problem from MP1:
*}

lemma Mp1_problem1: "|\<Turnstile>((A [\<and>] B) [\<longrightarrow>] (B [\<and>] A))"
  apply (rule bvalid_imp_bI)
  by (simp add: and_b_def)

text{*
Remove the \texttt{oops} from each problem and put in your own proof.

\begin{problem}(5 pts)
\end{problem}\vspace*{-2em}
*}
lemma problem1: "|\<Turnstile>((A [\<and>] B) [\<longrightarrow>] (([\<not>]B) [\<longrightarrow>] ([\<not>]A)))"
  apply (rule bvalid_imp_bI)
  by (simp add: and_b_def imp_b_def not_b_def)

lemma problem1_isar: "|\<Turnstile>((A [\<and>] B) [\<longrightarrow>] (([\<not>]B) [\<longrightarrow>] ([\<not>]A)))"
proof (rule bvalid_imp_bI)
  show "\<forall>s. (A [\<and>] B) s \<longrightarrow> ([\<not>]B [\<longrightarrow>] [\<not>]A) s"
  by (simp add: and_b_def imp_b_def not_b_def)
qed

text{*
\begin{problem}(5 pts)
\end{problem}\vspace*{-2em}
*}
lemma problem2: "|\<Turnstile>((A [\<longrightarrow>] B) [\<longrightarrow>] (([\<not>] B) [\<longrightarrow>] ([\<not>] A)))"
  apply (rule bvalid_imp_bI)
  by (auto simp add: imp_b_def not_b_def)

lemma problem2_isar: "|\<Turnstile>((A [\<longrightarrow>] B) [\<longrightarrow>] (([\<not>] B) [\<longrightarrow>] ([\<not>] A)))"
proof (rule bvalid_imp_bI)
  show "\<forall>s. (A [\<longrightarrow>] B) s \<longrightarrow> ([\<not>]B [\<longrightarrow>] [\<not>]A) s "
  by (auto simp add: imp_b_def not_b_def)
qed

text{*
\begin{problem}(5 pts)
\end{problem}\vspace*{-2em}
*}
lemma problem3: "|\<Turnstile>(([\<not>]A [\<or>] [\<not>]B) [\<longrightarrow>] ([\<not>](A [\<and>] B)))"
  apply (rule bvalid_imp_bI)
  by (simp add: and_b_def imp_b_def not_b_def or_b_def)

lemma problem3_isar: "|\<Turnstile>(([\<not>]A [\<or>] [\<not>]B) [\<longrightarrow>] ([\<not>](A [\<and>] B)))"
proof (rule bvalid_imp_bI)
  show "\<forall>s. ([\<not>]A [\<or>] [\<not>]B) s \<longrightarrow> ([\<not>](A [\<and>] B)) s"
  by (simp add: and_b_def imp_b_def not_b_def or_b_def)
qed

subsection{*Lifted Arithmetic Facts\label{laf}*}
text{*
For the next three problems, you may additionally wish to use definitions and
theorems in \texttt{lifted\_int\_data} as well as those in
\texttt{lifted\_predicate\_logic}.  In addition to \texttt{simp},
\texttt{clarsimp}, and \texttt{auto}, you may find \texttt{arith} sometimes
useful, once you have reduced the problem to ``ordinary'' arithmetic.  It
solves problems in linear arithmetic (no multiplying variables together).
Alternately, if you have reduced your problem to ``ordinary'' arithmetic,
you will probably find that Sledgehammer (the third tab in the list at the
bottom) generally can find a proof for you.  If you get stuck, don't waste
time thrashing; ask for help on piazza or in my office. 

Depending on how you attack these problems, you may be faced with showing
two functions taking states as arguments are equal.  You can turn this into
a ``ground'' equality between to values with\\\\
\texttt{apply (rule ext)}\\\\
The following is an example that was worked in class as a part of a larger
Hoare Logic Problem:
*}
lemma arith_example:
"|\<Turnstile> (($ ''p'' [=] $ ''i'' [\<times>] $ ''y'' [\<and>] $ ''i'' [\<le>] ($ ''x'') [\<and>]
          $ ''i'' [<] $ ''x'') [\<longrightarrow>]
     ($ ''p'' [+] $ ''y'' [=] ($ ''i'' [+] k 1) [\<times>] $ ''y'' [\<and>]
      $ ''i'' [+] k 1 [\<le>] $ ''x''))"
  apply (simp add: eq_b_def imp_b_def plus_e_def and_b_def  less_b_def
                   less_eq_b_def times_e_def k_def rev_app_def bvalid_def)
  by (simp add: distrib_right)

text{*
\begin{problem}(7 pts)
\end{problem}\vspace*{-2em}*}
lemma problem4: 
"|\<Turnstile>($''x'' [\<times>] ($''y'' [+] $''z'') [=] (($''x'' [\<times>] $''y'') [+] ($''x'' [\<times>]$''z'')))"
  apply (simp add: bvalid_def rev_app_def times_e_def plus_e_def eq_b_def)
by (simp add: int_distrib(2))

thm int_distrib(2)

lemma problem4_isar: 
"|\<Turnstile>($''x'' [\<times>] ($''y'' [+] $''z'') [=] (($''x'' [\<times>] $''y'') [+] ($''x'' [\<times>]$''z'')))"
proof (simp add: bvalid_def rev_app_def times_e_def plus_e_def eq_b_def)
  show "\<forall>s::string \<Rightarrow> int. s ''x'' * (s ''y'' + s ''z'') = s ''x'' * s ''y'' + s ''x'' * s ''z''"
    by (simp add: int_distrib(2))
qed

text{*
\begin{problem}(6 pts)
\end{problem}\vspace*{-2em}
*}
lemma problem5:
"|\<Turnstile> ((($ ''y'' [+] $ ''x'' [=] k (a + b)) [\<and>]
       ($ ''x'' [\<ge>] k 0) [\<and>] ([\<not>]($ ''x'' [>] k 0))) [\<longrightarrow>]
         ($ ''y'' [=] k (a + b)))"
   by (simp add: bvalid_def rev_app_def plus_e_def greater_eq_b_def eq_b_def
                    k_def greater_b_def not_b_def and_b_def imp_b_def)

text{*
\begin{problem}(8 pts)
\end{problem}\vspace*{-2em}
*}
lemma problem6:
"|\<Turnstile> ((($ ''y'' [=] $ ''a'') [\<and>] ([\<not>]($ ''y'' [mod] k 2 [=] k 0))) [\<longrightarrow>]
 (($ ''y'' [+] k 1 [\<ge>] $ ''a'') [\<and>] ($ ''y'' [+] k 1 [\<le>] $ ''a'' [+] k 1) [\<and>]
          (($ ''y'' [+] k 1) [mod] k 2 [=] k 0)))"
   apply (simp add: eq_b_def imp_b_def and_b_def less_eq_b_def greater_eq_b_def
                    not_b_def plus_e_def mod_e_def k_def rev_app_def bvalid_def)
  by (smt mod_add_cong mod_self one_mod_two_eq_one)

lemma problem6_iasr:
"|\<Turnstile> ((($ ''y'' [=] $ ''a'') [\<and>] ([\<not>]($ ''y'' [mod] k 2 [=] k 0))) [\<longrightarrow>]
 (($ ''y'' [+] k 1 [\<ge>] $ ''a'') [\<and>] ($ ''y'' [+] k 1 [\<le>] $ ''a'' [+] k 1) [\<and>]
          (($ ''y'' [+] k 1) [mod] k 2 [=] k 0)))"
proof (simp add: eq_b_def imp_b_def and_b_def less_eq_b_def greater_eq_b_def
                    not_b_def plus_e_def mod_e_def k_def rev_app_def bvalid_def)
  show "\<forall>s::string \<Rightarrow> int.
         s ''y'' = s ''a'' \<and> s ''y'' mod 2 = 1 \<longrightarrow> (s ''a'' + 1) mod 2 = 0 "
    by (smt mod_add_cong mod_self one_mod_two_eq_one)
qed

subsection{*Hoare Logic Proofs*}
text{*
In the next set of problems, you will want to rely upon the rules in
\texttt{Hoare\_SIMP} that define the relation \texttt{hprovable} describing
which Hoare triples are provable.  If you want Isabelle to figure out some of
the missing pieces for you, you may wish to alter the order in which you solve
the subgoals.  You may use \texttt{prefer} $n$ to select the $n^{th}$ subgoal
as the next one you will work on.
 
\begin{problem}(15 pts)
\end{problem}\vspace*{-2em}
*}
lemma problem7:
"{{$''y'' [=] $''a'' }}
IF $''y'' [mod] (k 2) [=] (k 0) THEN (''y'' ::= $''y'') ELSE (''y'' ::= $''y'' [+] (k 1)) FI
{{($''y'' [\<ge>] $''a'') [\<and>]
  ($''y'' [\<le>] ($''a'' [+] (k 1))) [\<and>]
  ($''y'' [mod] (k 2) [=] k 0)}}"
  apply (rule IfThenElseRule)
   apply (rule PreconditionStrengthening)
  defer
    apply (rule AssignmentAxiom)
   apply (rule PreconditionStrengthening)
    defer
    apply (rule AssignmentAxiom)
  apply simp
   apply (simp add: eq_b_def imp_b_def and_b_def less_eq_b_def greater_eq_b_def
                    plus_e_def k_def rev_app_def bvalid_def)
  apply simp
   apply (simp add: eq_b_def imp_b_def and_b_def less_eq_b_def greater_eq_b_def
                    not_b_def plus_e_def mod_e_def k_def rev_app_def bvalid_def)
  by (smt mod_add_cong mod_self one_mod_two_eq_one)

lemma problem7_isar:
"{{$''y'' [=] $''a'' }}
IF $''y'' [mod] (k 2) [=] (k 0) THEN (''y'' ::= $''y'') ELSE (''y'' ::= $''y'' [+] (k 1)) FI
{{($''y'' [\<ge>] $''a'') [\<and>]
  ($''y'' [\<le>] ($''a'' [+] (k 1))) [\<and>]
  ($''y'' [mod] (k 2) [=] k 0)}}"
proof (rule IfThenElseRule)
  show "{{$ ''y'' [=] $ ''a'' [\<and>]
      $ ''y'' [mod] k 2 [=]
      k 0}}''y'' ::= $ ''y''{{$ ''y'' [\<ge>] $ ''a'' [\<and>]
                              $ ''y'' [\<le>] $ ''a'' [+] k 1 [\<and>]
                              $ ''y'' [mod] k 2 [=] k 0}}"
  proof (rule PreconditionStrengthening)
--{*Isar won't help us out with figuring out what P is, so sometimes it is *}
--{*helpful to mix in a little apply style.  Here I used the proof above. *}
    show "{{(($ ''y'' [\<ge>] $ ''a'' [\<and>] $ ''y'' [\<le>] $ ''a'' [+] k 1 [\<and>]
           $ ''y'' [mod] k 2 [=] k 0)
          [''y''\<Leftarrow>$ ''y''])}}''y'' ::= $ ''y''{{$ ''y'' [\<ge>] $ ''a'' [\<and>]
                               $ ''y'' [\<le>] $ ''a'' [+] k 1 [\<and>]
                               $ ''y'' [mod] k 2 [=] k 0}}"
      by (rule AssignmentAxiom)
  next
    show "|\<Turnstile> (($ ''y'' [=] $ ''a'' [\<and>] $ ''y'' [mod] k 2 [=] k 0) [\<longrightarrow>]
         (($ ''y'' [\<ge>] $ ''a'' [\<and>] $ ''y'' [\<le>] $ ''a'' [+] k 1 [\<and>]
           $ ''y'' [mod] k 2 [=] k 0)
          [''y''\<Leftarrow>$ ''y'']))"
    proof simp
      show "|\<Turnstile> (($ ''y'' [=] $ ''a'' [\<and>] $ ''y'' [mod] k 2 [=] k 0) [\<longrightarrow>]
         ($ ''y'' [\<ge>] $ ''a'' [\<and>] $ ''y'' [\<le>] $ ''a'' [+] k 1 [\<and>]
          $ ''y'' [mod] k 2 [=] k 0))"
        by (simp add: eq_b_def imp_b_def and_b_def less_eq_b_def greater_eq_b_def
                    plus_e_def k_def rev_app_def bvalid_def)
    qed
  qed
next
  show "{{$ ''y'' [=] $ ''a'' [\<and>] [\<not>]($ ''y'' [mod] k 2 [=] k 0)}}
        ''y'' ::= $ ''y'' [+] k 1
        {{$ ''y'' [\<ge>] $ ''a'' [\<and>] $ ''y'' [\<le>] $ ''a'' [+] k 1 [\<and>]
                       $ ''y'' [mod] k 2 [=] k 0}}"
  proof (rule PreconditionStrengthening)
    show "{{(($ ''y'' [\<ge>] $ ''a'' [\<and>] $ ''y'' [\<le>] $ ''a'' [+] k 1 [\<and>]
           $ ''y'' [mod] k 2 [=] k 0)
          [''y''\<Leftarrow>$ ''y'' [+] k 1])}}''y'' ::= $ ''y'' [+]
                     k 1{{$ ''y'' [\<ge>] $ ''a'' [\<and>] $ ''y'' [\<le>] $ ''a'' [+] k 1 [\<and>]
                          $ ''y'' [mod] k 2 [=] k 0}}"
      by (rule AssignmentAxiom)
  next
    show "|\<Turnstile> (($ ''y'' [=] $ ''a'' [\<and>] [\<not>]($ ''y'' [mod] k 2 [=] k 0)) [\<longrightarrow>]
         (($ ''y'' [\<ge>] $ ''a'' [\<and>] $ ''y'' [\<le>] $ ''a'' [+] k 1 [\<and>]
           $ ''y'' [mod] k 2 [=] k 0)
          [''y''\<Leftarrow>$ ''y'' [+] k 1]))"
    proof simp
      show "|\<Turnstile> (($ ''y'' [=] $ ''a'' [\<and>] [\<not>]($ ''y'' [mod] k 2 [=] k 0)) [\<longrightarrow>]
         ($ ''y'' [+] k 1 [\<ge>] $ ''a'' [\<and>] $ ''y'' [+] k 1 [\<le>] $ ''a'' [+] k 1 [\<and>]
         ($ ''y'' [+] k 1) [mod] k 2 [=] k 0)) "
      proof (simp add: eq_b_def imp_b_def and_b_def less_eq_b_def greater_eq_b_def
                    not_b_def plus_e_def mod_e_def k_def rev_app_def bvalid_def)
        show "\<forall>s::string \<Rightarrow> int. 
               s ''y'' = s ''a'' \<and> s ''y'' mod 2 = 1 \<longrightarrow> (s ''a'' + 1) mod 2 = 0"
          by (smt mod_add_cong mod_self one_mod_two_eq_one)
      qed
    qed
  qed
qed

(*declare [[show_types = true]] *)
text{*
\begin{problem}(21 pts)
\end{problem}\vspace*{-2em}
*}
lemma problem8:
"{{$ ''y'' [=] k a [\<and>] $ ''x'' [=] k b [\<and>] k b [>] k 0}}
WHILE $ ''x'' [>] k 0 DO
(''y'' ::= $ ''y'' [+] k 1;;
 ''x'' ::= $ ''x'' [-] k 1)
OD
{{$ ''y'' [=] k (a + b)}}"

  apply (rule_tac Q' = "(($ ''y'' [+] $ ''x'' [=] k(a + b)) [\<and>]
                         ($ ''x'' [\<ge>] k 0)) [\<and>]
                        ([\<not>] ($ ''x'' [>] k 0))" in PostconditionWeakening)
   apply (simp add: bvalid_def rev_app_def plus_e_def greater_eq_b_def eq_b_def
                    k_def greater_b_def not_b_def and_b_def imp_b_def)
  apply (rule_tac P' = "(($ ''y'' [+] $ ''x'' [=] k(a + b)) [\<and>]
                         ($ ''x'' [\<ge>] k 0))" in PreconditionStrengthening)
   apply (simp add: bvalid_def rev_app_def plus_e_def greater_eq_b_def eq_b_def
                    k_def greater_b_def and_b_def imp_b_def)
  apply (rule WhileRule)
  apply (rule SequenceRule)
   prefer 2
   apply (rule AssignmentAxiom)
  apply simp
  apply (rule PreconditionStrengthening)
  prefer 2
   apply (rule AssignmentAxiom)
  apply simp
  by (simp add: bvalid_def rev_app_def plus_e_def minus_e_def greater_eq_b_def eq_b_def
                   k_def greater_b_def and_b_def imp_b_def)

lemma problem8_isar:
"{{$ ''y'' [=] k a [\<and>] $ ''x'' [=] k b [\<and>] k b [>] k 0}}
WHILE $ ''x'' [>] k 0 DO
(''y'' ::= $ ''y'' [+] k 1;;
 ''x'' ::= $ ''x'' [-] k 1)
OD
{{$ ''y'' [=] k (a + b)}}"
proof (rule_tac Q' = "(($ ''y'' [+] $ ''x'' [=] k(a + b)) [\<and>]
                         ($ ''x'' [\<ge>] k 0)) [\<and>]
                        ([\<not>] ($ ''x'' [>] k 0))" in PostconditionWeakening)
  show "|\<Turnstile> (($ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0 [\<and>]
          [\<not>]($ ''x'' [>] k 0)) [\<longrightarrow>]
         $ ''y'' [=] k (a + b))"
    by (simp add: bvalid_def rev_app_def plus_e_def greater_eq_b_def eq_b_def
                    k_def greater_b_def not_b_def and_b_def imp_b_def)
next
  show "{{$ ''y'' [=] k a [\<and>] $ ''x'' [=] k b [\<and>] k b [>] k 0}}WHILE $ ''x'' [>] k 0
    DO ''y'' ::= $ ''y'' [+] k 1;; ''x'' ::= $ ''x'' [-] k 1 OD
   {{$ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0 [\<and>] [\<not>]($ ''x'' [>] k 0)}}"
  proof (rule_tac P' = "(($ ''y'' [+] $ ''x'' [=] k(a + b)) [\<and>]
                         ($ ''x'' [\<ge>] k 0))" in PreconditionStrengthening)
    show "|\<Turnstile> (($ ''y'' [=] k a [\<and>] $ ''x'' [=] k b [\<and>] k b [>] k 0) [\<longrightarrow>]
         ($ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0))"
      by (simp add: bvalid_def rev_app_def plus_e_def greater_eq_b_def eq_b_def
                    k_def greater_b_def and_b_def imp_b_def)
  next
    show "{{$ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0}}
          WHILE $ ''x'' [>] k 0
          DO ''y'' ::= $ ''y'' [+] k 1;; ''x'' ::= $ ''x'' [-] k 1 OD
          {{$ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0 [\<and>]
           [\<not>]($ ''x'' [>] k 0) }} "
    proof (rule WhileRule)
      show "{{$ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0 [\<and>]
      $ ''x'' [>] k 0}}''y'' ::= $ ''y'' [+] k 1;;
    ''x'' ::= $ ''x'' [-]
              k 1{{$ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0}} "
      proof (rule SequenceRule)
        show "{{($ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0)
                [''x''\<Leftarrow>$ ''x'' [-] k 1]}}
              ''x'' ::= $ ''x'' [-]k 1
              {{$ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0}}"
          by (rule AssignmentAxiom)
      next
        show "{{$ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0 [\<and>]
      $ ''x'' [>]
      k 0}}''y'' ::= $ ''y'' [+]
                     k 1{{($ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0)
    [''x''\<Leftarrow>$ ''x'' [-] k 1]}}"
        proof simp
          show "{{$ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0 [\<and>]
      $ ''x'' [>] k 0}}
      ''y'' ::= $ ''y'' [+] k 1
                {{$ ''y'' [+] ($ ''x'' [-] k 1) [=] k (a + b) [\<and>]
                  $ ''x'' [-] k 1 [\<ge>] k 0}} "
          proof (rule PreconditionStrengthening)
            show "{{(($ ''y'' [+] ($ ''x'' [-] k 1) [=] k (a + b) [\<and>] $ ''x'' [-] k 1 [\<ge>] k 0)
          [''y''\<Leftarrow>$ ''y'' [+] k 1])}}''y'' ::= $ ''y'' [+]
                     k 1{{$ ''y'' [+] ($ ''x'' [-] k 1) [=] k (a + b) [\<and>]
                          $ ''x'' [-] k 1 [\<ge>] k 0}}"
              by (rule AssignmentAxiom)
          next
            show "|\<Turnstile> (($ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0 [\<and>]
          $ ''x'' [>] k 0) [\<longrightarrow>]
         (($ ''y'' [+] ($ ''x'' [-] k 1) [=] k (a + b) [\<and>] $ ''x'' [-] k 1 [\<ge>] k 0)
          [''y''\<Leftarrow>$ ''y'' [+] k 1]))"
            proof simp
              show "|\<Turnstile> (($ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0 [\<and>]
          $ ''x'' [>] k 0) [\<longrightarrow>]
         ($ ''y'' [+] k 1 [+] ($ ''x'' [-] k 1) [=] k (a + b) [\<and>]
          $ ''x'' [-] k 1 [\<ge>] k 0))"
                by (simp add: bvalid_def rev_app_def plus_e_def minus_e_def
                              greater_eq_b_def eq_b_def k_def greater_b_def
                              and_b_def imp_b_def)
            qed
          qed
        qed
      qed
    qed
  qed
qed


subsection{*Verification Conditions*}
text{*
Lastly, I ask you to redo \texttt{problem8}, but this time where you use none
of the rules defining \texttt{hprovable}, or the two derived rules of consequence,
but instead make use of the rules \texttt{alt\_ann\_provable\_provable},
\texttt{vcg\_and\_P} found in \texttt{Hoare\_ann\_SIMP}.  After that,
\texttt{simp} will remove the instances of \texttt{vcg} and \texttt{wp}, and
you are left with a problem like the ones in Subsection \ref{laf}.
*}

text{*
\begin{problem}(10 pts)
\end{problem}\vspace*{-2em}
*}
lemma problem9:
"{{$ ''y'' [=] k a [\<and>] $ ''x'' [=] k b [\<and>] k b [>] k 0}}
WHILE $ ''x'' [>] k 0 DO
(''y'' ::= $ ''y'' [+] k 1;;
 ''x'' ::= $ ''x'' [-] k 1)
OD
{{$ ''y'' [=] k (a + b)}}"

  apply (rule_tac C = "While $ ''x'' [>] k 0 
                       Inv ($ ''y'' [+] $ ''x'' [=] k(a + b))
                            [\<and>] ($ ''x'' [\<ge>] k 0)
                       Do
                         (''y'' :== $ ''y'' [+] k 1;-;
                          ''x'' :== $ ''x'' [-] k 1)
                       Od"
         in alt_ann_provable_provable)
   apply simp
  apply (rule vcg_and_P)
  apply simp
  by (simp add: bvalid_def rev_app_def plus_e_def minus_e_def greater_eq_b_def eq_b_def
                   k_def greater_b_def and_b_def imp_b_def not_b_def true_b_def)

lemma problem9_isar:
"{{$ ''y'' [=] k a [\<and>] $ ''x'' [=] k b [\<and>] k b [>] k 0}}
WHILE $ ''x'' [>] k 0 DO
(''y'' ::= $ ''y'' [+] k 1;;
 ''x'' ::= $ ''x'' [-] k 1)
OD
{{$ ''y'' [=] k (a + b)}}"
proof (rule_tac C = "While $ ''x'' [>] k 0 
                       Inv ($ ''y'' [+] $ ''x'' [=] k(a + b))
                            [\<and>] ($ ''x'' [\<ge>] k 0)
                       Do
                         (''y'' :== $ ''y'' [+] k 1;-;
                          ''x'' :== $ ''x'' [-] k 1)
                       Od"
         in alt_ann_provable_provable)
  show "WHILE $ ''x'' [>] k 0 DO ''y'' ::= $ ''y'' [+] k 1;; ''x'' ::= $ ''x'' [-] k 1
    OD =
    strip_annotations
     (While $ ''x'' [>] k 0 Inv $ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0
      Do ''y'' :== $ ''y'' [+] k 1 ;-; ''x'' :== $ ''x'' [-] k 1 Od)"
    by simp
next
  show "\<lbrace>$ ''y'' [=] k a [\<and>] $ ''x'' [=] k b [\<and>] k b [>] k 0\<rbrace>While $ ''x'' [>] k 0
    Inv $ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0
    Do ''y'' :== $ ''y'' [+] k 1 ;-; ''x'' :== $ ''x'' [-] k 1
    Od\<lbrace>$ ''y'' [=] k (a + b)\<rbrace>"
  proof (rule vcg_and_P)
    show "|\<Turnstile> ((($ ''y'' [=] k a [\<and>] $ ''x'' [=] k b [\<and>] k b [>] k 0) [\<longrightarrow>]
         (wp (While $ ''x'' [>] k 0
             Inv $ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0
             Do ''y'' :== $ ''y'' [+] k 1 ;-; ''x'' :== $ ''x'' [-] k 1 Od)
          ($ ''y'' [=] k (a + b)))) [\<and>]
         (vcg (While $ ''x'' [>] k 0
              Inv $ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0
              Do ''y'' :== $ ''y'' [+] k 1 ;-; ''x'' :== $ ''x'' [-] k 1 Od)
          ($ ''y'' [=] k (a + b)))) "
    proof simp
      show "|\<Turnstile> (((($ ''y'' [=] k a [\<and>] $ ''x'' [=] k b [\<and>] k b [>] k 0)) [\<longrightarrow>]
         ($ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0)) [\<and>]
         ((($ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0 [\<and>]
           $ ''x'' [>] k 0) [\<longrightarrow>]
          ($ ''y'' [+] k 1 [+] ($ ''x'' [-] k 1) [=] k (a + b) [\<and>]
          $ ''x'' [-] k 1 [\<ge>] k 0)) [\<and>]
          (true_b [\<and>] true_b) [\<and>]
          (($ ''y'' [+] $ ''x'' [=] k (a + b) [\<and>] $ ''x'' [\<ge>] k 0 [\<and>]
            [\<not>]($ ''x'' [>] k 0)) [\<longrightarrow>]
           ($ ''y'' [=] k (a + b)))))"
        by (simp add: bvalid_def rev_app_def plus_e_def minus_e_def
            greater_eq_b_def eq_b_def k_def greater_b_def and_b_def
            imp_b_def not_b_def true_b_def)
    qed
  qed
qed


subsection{*Extra Credit*}

text{*
\begin{problem}(10 pts)
\end{problem}\vspace*{-2em}
*}
lemma problem10:
"{{$ ''n'' [=] k a [\<and>] k a [>] k 0}}
''r'' ::= k 0;;
WHILE ($ ''n'' [>] k 0) DO
''r'' ::= $ ''r'' [+] $ ''n'';;
''n'' ::= $ ''n'' [-] k 1
OD
{{k 2 [\<times>] $ ''r'' [=] k (a * (a + 1))}}"
  
(* r + ((n * (n + 1)) / 2) = a * (a + 1) / 2 *)
(* (2 * r) + n * (n + 1) = a * (a + 1) *)
  apply (rule_tac C = "''r'' :== k 0 ;-;
                       (While $ ''n'' [>] k 0 
                        Inv ((k 2 [\<times>] $''r'') [+] ($''n'' [\<times>] ($''n'' [+] k 1))
                             [=] k(a * (a + 1)))
                             [\<and>] ($ ''n'' [\<ge>] k 0)
                        Do
                          (''r'' :== $ ''r'' [+] $ ''n'';-;
                           ''n'' :== $ ''n'' [-] k 1)
                        Od)"
         in alt_ann_provable_provable)
   apply simp
  apply (rule vcg_and_P)
  apply simp
  apply (simp add: bvalid_def rev_app_def plus_e_def minus_e_def times_e_def
                   greater_eq_b_def eq_b_def
                   k_def greater_b_def and_b_def imp_b_def not_b_def true_b_def)
  apply auto
  apply (rule trans, rule sym)
   prefer 2
   apply assumption
  by (simp only:  Rings.ring_class.ring_distribs)


lemma problem10_isar:
"{{$ ''n'' [=] k a [\<and>] k a [>] k 0}}
''r'' ::= k 0;;
WHILE ($ ''n'' [>] k 0) DO
''r'' ::= $ ''r'' [+] $ ''n'';;
''n'' ::= $ ''n'' [-] k 1
OD
{{k 2 [\<times>] $ ''r'' [=] k (a * (a + 1))}}"
proof (rule_tac C = "''r'' :== k 0 ;-;
                       (While $ ''n'' [>] k 0 
                        Inv ((k 2 [\<times>] $''r'') [+] ($''n'' [\<times>] ($''n'' [+] k 1))
                             [=] k(a * (a + 1)))
                             [\<and>] ($ ''n'' [\<ge>] k 0)
                        Do
                          (''r'' :== $ ''r'' [+] $ ''n'';-;
                           ''n'' :== $ ''n'' [-] k 1)
                        Od)"
         in alt_ann_provable_provable)
  show "''r'' ::= k 0;; WHILE $ ''n'' [>] k 0 DO ''r'' ::= $ ''r'' [+] $ ''n'';;
    ''n'' ::= $ ''n'' [-] k 1 OD =
    strip_annotations
     (''r'' :== k 0 ;-;
      (While $ ''n'' [>] k 0
       Inv k 2 [\<times>] $ ''r'' [+] ($ ''n'' [\<times>] ($ ''n'' [+] k 1)) [=]
           k (a * (a + 1)) [\<and>]
           $ ''n'' [\<ge>] k 0
       Do ''r'' :== $ ''r'' [+] $ ''n'' ;-; ''n'' :== $ ''n'' [-] k 1 Od))"
    by simp
next
  show "\<lbrace>$ ''n'' [=] k a [\<and>]
     k a [>]
     k 0\<rbrace>''r'' :== k 0 ;-;
         (While $ ''n'' [>] k 0
          Inv k 2 [\<times>] $ ''r'' [+] ($ ''n'' [\<times>] ($ ''n'' [+] k 1)) [=]
              k (a * (a + 1)) [\<and>]
              $ ''n'' [\<ge>] k 0
          Do ''r'' :== $ ''r'' [+] $ ''n'' ;-; ''n'' :== $ ''n'' [-] k 1
          Od)\<lbrace>k 2 [\<times>] $ ''r'' [=] k (a * (a + 1))\<rbrace> "
  proof (rule vcg_and_P)
    show "|\<Turnstile> ((($ ''n'' [=] k a [\<and>] k a [>] k 0) [\<longrightarrow>]
         (wp (''r'' :== k 0 ;-;
             (While $ ''n'' [>] k 0
              Inv k 2 [\<times>] $ ''r'' [+] ($ ''n'' [\<times>] ($ ''n'' [+] k 1)) [=]
                  k (a * (a + 1)) [\<and>]
                  $ ''n'' [\<ge>] k 0
              Do ''r'' :== $ ''r'' [+] $ ''n'' ;-; ''n'' :== $ ''n'' [-] k 1 Od))
          (k 2 [\<times>] $ ''r'' [=] k (a * (a + 1))))) [\<and>]
         (vcg (''r'' :== k 0 ;-;
              (While $ ''n'' [>] k 0
               Inv k 2 [\<times>] $ ''r'' [+] ($ ''n'' [\<times>] ($ ''n'' [+] k 1)) [=]
                   k (a * (a + 1)) [\<and>]
                   $ ''n'' [\<ge>] k 0
               Do ''r'' :== $ ''r'' [+] $ ''n'' ;-; ''n'' :== $ ''n'' [-] k 1 Od))
          (k 2 [\<times>] $ ''r'' [=] k (a * (a + 1)))))"
    proof simp
      show "|\<Turnstile> ((($ ''n'' [=] k a [\<and>] k a [>] k 0) [\<longrightarrow>]
         (k 2 [\<times>] k 0 [+] ($ ''n'' [\<times>] ($ ''n'' [+] k 1)) [=] k (a * (a + 1)) [\<and>]
         $ ''n'' [\<ge>] k 0)) [\<and>]
         (true_b [\<and>]
          (((k 2 [\<times>] $ ''r'' [+] ($ ''n'' [\<times>] ($ ''n'' [+] k 1)) [=]
            k (a * (a + 1)) [\<and>]
            $ ''n'' [\<ge>] k 0 [\<and>]
            $ ''n'' [>] k 0) [\<longrightarrow>]
           (k 2 [\<times>] ($ ''r'' [+] $ ''n'') [+]
           ($ ''n'' [-] k 1 [\<times>] ($ ''n'' [-] k 1 [+] k 1)) [=]
           k (a * (a + 1)) [\<and>]
           $ ''n'' [-] k 1 [\<ge>] k 0)) [\<and>]
           (true_b [\<and>] true_b) [\<and>]
           ((((k 2 [\<times>] $ ''r'' [+] ($ ''n'' [\<times>] ($ ''n'' [+] k 1)) [=]
             k (a * (a + 1))) [\<and>]
             ($ ''n'' [\<ge>] k 0) [\<and>]
            ( [\<not>]($ ''n'' [>] k 0)))) [\<longrightarrow>]
            (k 2 [\<times>] $ ''r'' [=] k (a * (a + 1))))))) "
      proof (simp add: bvalid_def rev_app_def plus_e_def minus_e_def times_e_def
                   greater_eq_b_def eq_b_def
                   k_def greater_b_def and_b_def imp_b_def not_b_def true_b_def)
        show " \<forall>s. (2 * s ''r'' + s ''n'' * (s ''n'' + 1) = a * (a + 1) \<and>
         0 \<le> s ''n'' \<and> 0 < s ''n'' \<longrightarrow>
         2 * s ''r'' + 2 * s ''n'' + (s ''n'' - 1) * s ''n'' = a * (a + 1)) \<and>
        (2 * s ''r'' + s ''n'' * (s ''n'' + 1) = a * (a + 1) \<and>
         0 \<le> s ''n'' \<and> \<not> 0 < s ''n'' \<longrightarrow>
         2 * s ''r'' = a * (a + 1))"
        proof auto
          fix s::"string \<Rightarrow> int"
          assume A1: "2 * s ''r'' + s ''n'' * (s ''n'' + 1) = a * (a + 1)"
          and A2: "0 < s ''n''"
          then 
          show "2 * s ''r'' + 2 * s ''n'' + (s ''n'' - 1) * s ''n'' = a * (a + 1)"
          proof (rule_tac trans, rule_tac sym)
            from A1
            show "2 * s ''r'' + s ''n'' * (s ''n'' + 1) = a * (a + 1) " by assumption
          next
            show "(2::int) * s ''r'' + s ''n'' * (s ''n'' + 1) =
                  2 * s ''r'' + 2 * s ''n'' + (s ''n'' - 1) * s ''n''"
              by (simp only:  Rings.ring_class.ring_distribs)
          qed
        qed
      qed
    qed
  qed
qed

(*<*)
end
(*>*)
