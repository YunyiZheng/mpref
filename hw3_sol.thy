theory hw3_sol
imports Main
begin

lemma p4: "(\<forall> x. \<forall> y. P(x) \<longrightarrow> Q(y)) \<longrightarrow> ((\<exists> x. P(x)) \<longrightarrow>  (\<forall> y. Q(y)))"
  apply (rule impI)
  apply (rule impI)
  apply (rule allI)
  apply (erule exE)
  apply (erule_tac x = "x" in allE)
  apply (erule_tac x = "y" in allE)
  by (erule impE)

lemma p5: "(\<forall> x. \<forall> y. P(x) \<and> P(y)) \<longrightarrow> ((\<forall> x. P(x)) \<and>  (\<forall> y. P(y)))"
  apply (rule impI)
  apply (rule conjI)
  apply (rule allI)
  apply (erule_tac x = "x" in allE)
  apply (erule allE) 
  apply (erule conjE)
  apply assumption
  apply (rule allI)
  apply (erule_tac x = "y" in allE)
  apply (erule allE)
  by (erule conjE)

end
