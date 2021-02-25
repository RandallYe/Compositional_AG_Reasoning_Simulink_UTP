section {* Block Laws  \label{sec:block_laws} *}
text {* In this section, many theorems and laws are proved to facilitate application of our theories
in Simulink block diagrams. *}

theory simu_contract_real_laws
  imports
    simu_contract_real
begin

-- {* timeout in seconds *}
declare [[ smt_timeout = 600 ]]

subsection {* Additional Laws *}
text {* @{text "list_len_avail"}: there always exists some signals that could have a specific size. *}
lemma list_len_avail:
  "\<forall>x\<ge>0. (\<exists>(xx::nat\<Rightarrow>real list). \<forall>n. length (xx n) = x)"
  apply (rule allI)
  apply (auto)
  apply (induct_tac x)
  apply (rule_tac x = "\<lambda>na. []" in exI, simp)
  apply (auto)
  by (rule_tac x = "\<lambda>na. 0#(xx na)" in exI, simp)

text {* @{text "list_len_avail"}: there always exists some signals that could have a specific size and
 the value of each signal is equal to an arbitrary real number. *}
lemma list_len_avail':
  "\<forall>r::real. \<forall>x\<ge>0. (\<exists>(xx::nat\<Rightarrow>real list). (\<forall>n. (length (xx n) = x) \<and> (\<forall>y::nat<x. ((xx n)!y = r))))"
  apply (rule allI)
  apply (auto)
  apply (induct_tac x)
  apply (rule_tac x = "\<lambda>na. []" in exI, simp)
  apply (auto)
  apply (rule_tac x = "\<lambda>na. r#(xx na)" in exI, simp)
  using less_Suc_eq_0_disj by auto

text {* @{text "sum_hd_signal"} sums up a signal's current value and all past values. *}
fun sum_hd_signal:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> real" where
"sum_hd_signal x 0 = hd(x 0)" |
"sum_hd_signal x (Suc n) = hd(x (Suc n)) + sum_hd_signal x (n)"

text {* @{text "remove_at"} removes the ith element from a list. *}
abbreviation "remove_at \<equiv> (\<lambda>lst i. (take (i) lst)@(drop (i+1) lst))"

lemma "remove_at [] 1 = []" by simp

lemma "remove_at [2,3,4] 1 = [2,4]" by simp

text {* @{text "fun_eq"}: two functions are equal as long as they are equal in all their domains 
(total functions). *}
lemma fun_eq:
  assumes "\<forall>x. f x = g x"
  shows "f = g"
  by (simp add: assms ext)

text {* @{text "fun_eq'"}: two functions are equal in all their domains then they are equal functions.
(total functions). *}
lemma fun_eq':
  assumes "f = g"
  shows "\<forall>x. (f x = g x)"
  by (simp add: assms)

lemma fun_neq:
  assumes "\<forall>x. \<not> (f x = g x)"
  shows "\<not> f = g"
  using assms by auto

text {* @{text "ref_eq"}: two predicates are equal as long as they are refined by each other. *}
lemma ref_eq: 
  assumes "P \<sqsubseteq> Q"
  assumes "Q \<sqsubseteq> P"
  shows "P = Q"
  by (simp add: antisym assms(1) assms(2))

lemma hd_drop_m: 
  "\<forall>(x::nat \<Rightarrow> real list) n::nat. length(x n) > m \<longrightarrow> (hd (drop m (x n)) = x n!m)"
  using hd_drop_conv_nth by blast

lemma hd_take_m: 
  "m > 0 \<longrightarrow> (\<forall>(x::nat \<Rightarrow> real list) n::nat. (hd (take m (x n)) = hd(x n)))"
  by (metis append_take_drop_id hd_append2 less_numeral_extra(3) take_eq_Nil)

lemma hd_tl_take_m: 
  "m > 1 \<longrightarrow> (\<forall>(x::nat \<Rightarrow> real list) n::nat. (hd (tl (take m (x n))) = hd(tl(x n))))"
    by (metis hd_conv_nth less_numeral_extra(3) nth_take take_eq_Nil tl_take zero_less_diff)

subsection {* SimBlock healthiness *}

lemma SimBlock_FBlock [simblock_healthy]:
  assumes s1: "\<exists>inouts\<^sub>v inouts\<^sub>v'. 
      \<forall>x. length(inouts\<^sub>v' x) = n \<and> 
          length(inouts\<^sub>v x) = m \<and> 
          f inouts\<^sub>v x = inouts\<^sub>v' x"
  assumes s2: "\<forall>x na. length(x na) = m \<longrightarrow> length(f x na) = n"
  shows "SimBlock m n (FBlock (\<lambda>x n. True) m n f)"
  apply (simp add: SimBlock_def FBlock_def)
  apply (rel_auto)
  using s1 apply blast
  by (simp add: s2)

lemma SimBlock_FBlock' [simblock_healthy]:
  assumes s1: "\<exists>inouts\<^sub>v. (\<forall>x. p1 inouts\<^sub>v x) \<and>
      (\<exists> inouts\<^sub>v'. 
      \<forall>x. length(inouts\<^sub>v' x) = n \<and> 
          length(inouts\<^sub>v x) = m \<and> 
          f inouts\<^sub>v x = inouts\<^sub>v' x)"
  assumes s2: "\<forall>x na. length(x na) = m \<longrightarrow> length(f x na) = n"
  shows "SimBlock m n (FBlock (p1) m n f)"
  apply (simp add: SimBlock_def FBlock_def)
  apply (rel_auto)
  using s1 s2 by blast

lemma SimBlock_FBlock_fn [simblock_healthy]:
  assumes s1: "SimBlock m n (FBlock (\<lambda>x n. True) m n f)"
  shows "(\<forall>x xa. length(x xa) = m \<longrightarrow> length(f x xa) = n)"
  proof -
    have 1: "PrePost((FBlock (\<lambda>x n. True) m n f)) \<noteq> false"
      using s1 SimBlock_def
      by blast
    then show ?thesis
      apply (simp add: FBlock_def)
      apply (rel_simp)
    done
  qed

lemma SimBlock_FBlock_fn' [simblock_healthy]:
  assumes s1: "SimBlock m n (FBlock (p) m n f)"
  shows "(\<forall>x xa. length(x xa) = m \<longrightarrow> length(f x xa) = n)"
  proof -
    have 1: "PrePost((FBlock (p) m n f)) \<noteq> false"
      using s1 SimBlock_def
      by blast
    then show ?thesis
      apply (simp add: FBlock_def)
      apply (rel_simp)
    done
  qed

lemma SimBlock_FBlock_p [simblock_healthy]:
  assumes s1: "SimBlock m n (FBlock (p) m n f)"
  shows "\<exists>inouts\<^sub>v . \<forall>x. p inouts\<^sub>v x \<and> length(inouts\<^sub>v x) = m"
  proof -
    have 1: "PrePost((FBlock (p) m n f)) \<noteq> false"
      using s1 SimBlock_def
      by blast
    then show ?thesis
      apply (simp add: FBlock_def)
      apply (rel_simp)
      by blast
  qed

lemma SimBlock_FBlock_p_f [simblock_healthy]:
  assumes s1: "SimBlock m n (FBlock (p) m n f)"
  shows "\<exists>inouts\<^sub>v . \<forall>x. p inouts\<^sub>v x \<and> 
    (\<exists>inouts\<^sub>v'. \<forall>x. length(inouts\<^sub>v' x) = n \<and> length(inouts\<^sub>v x) = m \<and> f inouts\<^sub>v x = inouts\<^sub>v' x)"
  proof -
    have 1: "PrePost((FBlock (p) m n f)) \<noteq> false"
      using s1 SimBlock_def 
      by blast
    then show ?thesis
      apply (simp add: FBlock_def)
      apply (rel_simp)
      by blast
  qed
(*
lemma SimBlock_FBlock_p_f' [simblock_healthy]:
  assumes s1: "SimBlock m n (FBlock (\<lambda>x n. p x n \<and> length(x n) = m) m n f)"
  shows "\<forall>inouts\<^sub>v. ((\<forall>x. p inouts\<^sub>v x \<and> length(inouts\<^sub>v x) = m) \<longrightarrow> 
    (\<exists>inouts\<^sub>v'. \<forall>x. length(inouts\<^sub>v' x) = n \<and> length(inouts\<^sub>v x) = m \<and> f inouts\<^sub>v x = inouts\<^sub>v' x))"
  proof -
    have 1: "PrePost((FBlock (\<lambda>x n. p x n \<and> length(x n) = m) m n f)) \<noteq> false"
      using s1 SimBlock_def 
      by blast
    then have "\<exists>inouts\<^sub>v.
       (\<forall>x. p inouts\<^sub>v x \<and> length(inouts\<^sub>v x) = m) \<and>
       (\<exists>inouts\<^sub>v'. \<forall>x. length(inouts\<^sub>v' x) = n \<and> length(inouts\<^sub>v x) = m \<and> f inouts\<^sub>v x = inouts\<^sub>v' x) \<and>
       (\<forall>x xa. length(f x xa) = n)"
      apply (simp add: FBlock_def)
      by (rel_simp)
    then show ?thesis
      apply (simp)
      apply (rule allI)
  qed
*)
  
lemma FBlock_eq: 
  assumes "f1 = f2"
  shows "FBlock p_f m n f1 = FBlock p_f m n f2"
  using assms by simp

lemma FBlock_eq': 
  assumes "\<forall>(x::nat \<Rightarrow> real list) n. length(x n) = m \<longrightarrow> f1 x n = f2 x n"
  shows "FBlock p_f m n f1 = FBlock p_f m n f2"
  apply (simp add: FBlock_def)
  apply (rule ref_eq)
  apply (rel_simp)
  using assms apply simp
  apply (rel_simp)
  using assms by metis

lemma FBlock_eq'': 
  assumes s1: "\<forall>(x::nat \<Rightarrow> real list) n. (\<forall>na. length(x na) = m) \<longrightarrow> f1 x n = f2 x n"
  assumes s2: "\<forall>(x::nat \<Rightarrow> real list) na. length(f1 x na) = n"
  assumes s3: "\<forall>(x::nat \<Rightarrow> real list) na. length(f2 x na) = n"
  shows "FBlock p_f m n f1 = FBlock p_f m n f2"
  apply (simp add: FBlock_def)
  apply (rule ref_eq)
  apply (rel_simp)
  apply (rule conjI)
  apply (simp add: assms)
  using assms apply blast
  apply (rel_simp)
  using assms by metis

subsection {* inps and outps *}
lemma inps_P: 
  assumes "SimBlock m n P"
  shows "inps P = m"
  using assms inps_outps by auto

lemma outps_P: 
  assumes "SimBlock m n P"
  shows "outps P = n"
  using assms inps_outps by auto

lemma SimBlock_implies_not_PQ [simblock_healthy]:
  assumes s1: "SimBlock m n (P \<turnstile>\<^sub>n Q)"
  shows "(\<lceil>P\<rceil>\<^sub>< \<and> Q) \<noteq> false"
  using SimBlock_def s1 by auto

lemma SimBlock_implies_not_P [simblock_healthy]:
  assumes s1: "SimBlock m n (P \<turnstile>\<^sub>n Q)"
  shows "\<lceil>P\<rceil>\<^sub>< \<noteq> false"
  using SimBlock_def s1
  by (metis SimBlock_implies_not_PQ aext_false ndesign_def ndesign_refinement' true_conj_zero(1) 
    utp_pred_laws.bot.extremum utp_pred_laws.inf.orderE)

lemma SimBlock_implies_not_P' [simblock_healthy]:
  assumes s1: "SimBlock m n (P \<turnstile>\<^sub>n Q)"
  shows "P \<noteq> false"
  using SimBlock_def s1
  by (metis SimBlock_implies_not_PQ aext_false ndesign_def  
    utp_pred_laws.bot.extremum utp_pred_laws.inf.orderE)

lemma SimBlock_implies_not_P'' [simblock_healthy]:
  assumes s1: "SimBlock m n (P \<turnstile>\<^sub>n Q)"
  shows "\<exists>inouts\<^sub>v inouts\<^sub>v'. \<lbrakk>\<lceil>P\<rceil>\<^sub><\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>)"
  using SimBlock_implies_not_P
  by (metis (mono_tags, hide_lams) bot_bool_def bot_uexpr.rep_eq false_upred_def old.unit.exhaust s1 
    sim_state.cases_scheme surj_pair udeduct_eqI)

lemma SimBlock_implies_not_P_cond [simblock_healthy]:
  assumes s1: "SimBlock m n (P \<turnstile>\<^sub>r Q)"
  assumes s2: "out\<alpha> \<sharp> P"
  shows "\<forall>inouts\<^sub>v inouts\<^sub>v' inouts\<^sub>v''.
       \<lbrakk>P\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v''\<rparr>) = \<lbrakk>P\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>)"
  using SimBlock_implies_not_P s1 s2 
  by (rel_simp)

lemma SimBlock_implies_not_Q [simblock_healthy]:
  assumes s1: "SimBlock m n (P \<turnstile>\<^sub>n Q)"
  shows "Q \<noteq> false"
  using SimBlock_def s1 by auto

lemma SimBlock_implies_not_Q' [simblock_healthy]:
  assumes s1: "SimBlock m n (P \<turnstile>\<^sub>n Q)"
  shows "\<exists>inouts\<^sub>v inouts\<^sub>v'. \<lbrakk>Q\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>)"
  using SimBlock_implies_not_Q
  by (metis (mono_tags, hide_lams) bot_bool_def bot_uexpr.rep_eq false_upred_def old.unit.exhaust s1 
    sim_state.cases_scheme surj_pair udeduct_eqI)

lemma SimBlock_implies_not_PQ' [simblock_healthy]:
  assumes s1: "SimBlock m n (P \<turnstile>\<^sub>n Q)"
  shows "\<exists>inouts\<^sub>v inouts\<^sub>v'. (\<lbrakk>P\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>) \<and> 
      \<lbrakk>Q\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>))"
  using s1 SimBlock_implies_not_PQ apply (rel_simp)
  done

lemma SimBlock_implies_mP [simblock_healthy]:
  assumes s1: "SimBlock m n (P \<turnstile>\<^sub>n Q)"
  shows "\<forall>inouts\<^sub>v inouts\<^sub>v' x.
       \<lbrakk>P\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>) \<longrightarrow>
       \<lbrakk>Q\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow> 
       length(inouts\<^sub>v x) = m"
  proof -
    from s1 have 1:"((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m\<guillemotright>) \<sqsubseteq> Dom(PrePost((P \<turnstile>\<^sub>n Q))))"
      by (simp add: SimBlock_def)
    then show ?thesis
      by (rel_auto)
  qed

lemma SimBlock_implies_Qn [simblock_healthy]:
  assumes s1: "SimBlock m n (P \<turnstile>\<^sub>n Q)"
  shows "\<forall>inouts\<^sub>v inouts\<^sub>v' x.
       \<lbrakk>P\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>) \<longrightarrow>
       \<lbrakk>Q\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow> 
       length(inouts\<^sub>v' x) = n"
  proof -
    from s1 have 1:"((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n\<guillemotright>) \<sqsubseteq> Ran(PrePost((P \<turnstile>\<^sub>n Q))))"
      by (simp add: SimBlock_def)
    then show ?thesis
      by (rel_auto)
  qed

lemma sim_refine_implies_inps_outps_eq:
  assumes s1: "SimBlock m1 n1 (P)"
  assumes s2: "SimBlock m2 n2 (Q)"
  assumes s3: "(P) \<sqsubseteq> (Q)"
  assumes s4: "(pre\<^sub>D(P) \<and> post\<^sub>D(Q)) \<noteq> false"
  shows "m1 = m2 \<and> n1 = n2"
  proof -
    have ref_des: "pre\<^sub>D(Q) \<sqsubseteq> pre\<^sub>D(P) \<and> post\<^sub>D(P) \<sqsubseteq> (pre\<^sub>D(P) \<and> post\<^sub>D(Q))"
      using s3
      by (simp add: design_refine_thms(1) design_refine_thms(2) refBy_order)
    have pred_1: "PrePost(P)  = (pre\<^sub>D(P) \<and> post\<^sub>D(P))"
      apply (simp)
    done
    have pred_2: "PrePost(Q) = (pre\<^sub>D(Q) \<and> post\<^sub>D(Q))"
      apply (simp)
    done
    have pred_1_not_false: "(pre\<^sub>D(P) \<and> post\<^sub>D(P)) \<noteq> false"
      using SimBlock_def s1 by force
    have pred_2_not_false: "(pre\<^sub>D(Q) \<and> post\<^sub>D(Q)) \<noteq> false"
      using SimBlock_def s2 by force
    have ref_inps_1: "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m1\<guillemotright>) \<sqsubseteq> Dom((pre\<^sub>D(P) \<and> post\<^sub>D(P))))"
      using s1 apply (simp add: SimBlock_def)
    done
    then have ref_inps_12: "... \<sqsubseteq> Dom((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))"
      apply (simp add: "ref_des" Dom_def)
      by (smt "ref_des" arestr.rep_eq conj_upred_def ex.rep_eq inf_bool_def inf_uexpr.rep_eq upred_ref_iff)
    have ref_inps_2: "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m2\<guillemotright>) \<sqsubseteq> Dom((pre\<^sub>D(Q) \<and> post\<^sub>D(Q))))"
      using s2 apply (simp add: SimBlock_def)
    done
    have ref_p2_p1: "Dom((pre\<^sub>D(Q) \<and> post\<^sub>D(Q))) \<sqsubseteq> Dom((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))" 
      apply (simp add: Dom_def)
      by (smt "ref_des" aext_mono arestr_and order_refl utp_pred_laws.ex_mono utp_pred_laws.inf.absorb_iff2 utp_pred_laws.inf_mono)
    from ref_p2_p1 and ref_inps_2 have ref_inps_2_p1: "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m2\<guillemotright>) \<sqsubseteq> Dom((pre\<^sub>D(P) \<and> post\<^sub>D(Q))))"
      by simp
    from ref_inps_2_p1 have P1_Q2_implies_m2: "(\<forall>b. \<lbrakk>Dom((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))\<rbrakk>\<^sub>e b \<longrightarrow> \<lbrakk>(\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m2\<guillemotright>)\<rbrakk>\<^sub>e b)" 
      apply (simp add: upred_ref_iff)
    done
    from ref_inps_12 have P1_Q2_implies_m1: "(\<forall>b. \<lbrakk>Dom((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))\<rbrakk>\<^sub>e b \<longrightarrow> \<lbrakk>(\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m1\<guillemotright>)\<rbrakk>\<^sub>e b)" 
      apply (simp add: upred_ref_iff)
    done
    from P1_Q2_implies_m1 and P1_Q2_implies_m2 have P1_Q2_implies_m2_m1:
      "\<forall>b. \<lbrakk>Dom((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))\<rbrakk>\<^sub>e b \<longrightarrow> (\<lbrakk>(\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m2\<guillemotright>)\<rbrakk>\<^sub>e b \<and> \<lbrakk>(\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m1\<guillemotright>)\<rbrakk>\<^sub>e b)"
      by blast
    then have P1_Q2_implies_m2_m1_1: "\<forall>b. \<lbrakk>Dom((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))\<rbrakk>\<^sub>e b \<longrightarrow> (\<lbrakk>(\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m2\<guillemotright>)\<and> (\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m1\<guillemotright>)\<rbrakk>\<^sub>e b)"
      by (simp add: conj_implies2)
    have forall_comb: "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m2\<guillemotright>)\<and> (\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m1\<guillemotright>)) = 
          (\<^bold>\<forall> na \<bullet> ((#\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m2\<guillemotright>) \<and> (#\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m1\<guillemotright>)))"
      apply (rel_auto)
    done
    from P1_Q2_implies_m2_m1_1 have P1_Q2_implies_m2_m1_2:
      "\<forall>b. \<lbrakk>Dom((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))\<rbrakk>\<^sub>e b \<longrightarrow> (\<lbrakk>(\<^bold>\<forall> na \<bullet> ((#\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m2\<guillemotright>) \<and> (#\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m1\<guillemotright>)))\<rbrakk>\<^sub>e b)"
      by (simp add: forall_comb)
    have m1_m2_eq: "m2 = m1"
      proof (rule ccontr)
        assume ss1: "m2 \<noteq> m1"
        have conj_false: "(\<^bold>\<forall> na \<bullet> ((#\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m2\<guillemotright>) \<and> (#\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m1\<guillemotright>))) = false"
          using ss1 apply (rel_auto)
        done
        have imp_false: "\<forall>b. \<lbrakk>Dom((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))\<rbrakk>\<^sub>e b \<longrightarrow> (\<lbrakk>false\<rbrakk>\<^sub>e b)"
          using P1_Q2_implies_m2_m1_2 
          apply (simp add: "conj_false")
        done
        have dom_false: "Dom((pre\<^sub>D(P) \<and> post\<^sub>D(Q))) = false"
          by (metis imp_false true_conj_zero(2) udeduct_refineI utp_pred_laws.inf.orderE utp_pred_laws.inf_commute)
        have P1_Q2_false: "(pre\<^sub>D(P) \<and> post\<^sub>D(Q)) = false"
          by (metis assume_Dom assume_false dom_false seqr_left_zero)
        show "False"
          using s4 apply (simp add: P1_Q2_false)
        done
      qed
    (* n1 = n2 *)
    have ref_inps_1': "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n1\<guillemotright>) \<sqsubseteq> Ran((pre\<^sub>D(P) \<and> post\<^sub>D(P))))"
      using s1 apply (simp add: SimBlock_def)
    done
    then have ref_inps_12': "... \<sqsubseteq> Ran((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))"
      apply (simp add: "ref_des" Ran_def)
      by (smt "ref_des" arestr.rep_eq conj_upred_def ex.rep_eq inf_bool_def inf_uexpr.rep_eq upred_ref_iff)
    have ref_inps_2': "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n2\<guillemotright>) \<sqsubseteq> Ran((pre\<^sub>D(Q) \<and> post\<^sub>D(Q))))"
      using s2 apply (simp add: SimBlock_def)
    done
    have ref_p2_p1': "Ran((pre\<^sub>D(Q) \<and> post\<^sub>D(Q))) \<sqsubseteq> Ran((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))" 
      apply (simp add: Ran_def)
      by (smt "ref_des" aext_mono arestr_and order_refl utp_pred_laws.ex_mono utp_pred_laws.inf.absorb_iff2 utp_pred_laws.inf_mono)
    from ref_p2_p1' and ref_inps_2' have ref_inps_2_p1': "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n2\<guillemotright>) \<sqsubseteq> Ran((pre\<^sub>D(P) \<and> post\<^sub>D(Q))))"
      by simp
    from ref_inps_2_p1' have P1_Q2_implies_n2: "(\<forall>b. \<lbrakk>Ran((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))\<rbrakk>\<^sub>e b \<longrightarrow> \<lbrakk>(\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n2\<guillemotright>)\<rbrakk>\<^sub>e b)" 
      apply (simp add: upred_ref_iff)
    done
    from ref_inps_12' have P1_Q2_implies_n1: "(\<forall>b. \<lbrakk>Ran((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))\<rbrakk>\<^sub>e b \<longrightarrow> \<lbrakk>(\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n1\<guillemotright>)\<rbrakk>\<^sub>e b)" 
      apply (simp add: upred_ref_iff)
    done
    from P1_Q2_implies_n1 and P1_Q2_implies_n2 have P1_Q2_implies_n2_n1:
      "\<forall>b. \<lbrakk>Ran((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))\<rbrakk>\<^sub>e b \<longrightarrow> (\<lbrakk>(\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n2\<guillemotright>)\<rbrakk>\<^sub>e b \<and> \<lbrakk>(\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n1\<guillemotright>)\<rbrakk>\<^sub>e b)"
      by blast
    then have P1_Q2_implies_n2_n1_1: 
      "\<forall>b. \<lbrakk>Ran((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))\<rbrakk>\<^sub>e b \<longrightarrow> (\<lbrakk>(\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n2\<guillemotright>)\<and> (\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n1\<guillemotright>)\<rbrakk>\<^sub>e b)"
      by (simp add: conj_implies2)
    have forall_comb': "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n2\<guillemotright>)\<and> (\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n1\<guillemotright>)) = 
          (\<^bold>\<forall> na \<bullet> ((#\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n2\<guillemotright>) \<and> (#\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n1\<guillemotright>)))"
      apply (rel_auto)
    done
    from P1_Q2_implies_n2_n1_1 have P1_Q2_implies_n2_n1_2:
      "\<forall>b. \<lbrakk>Ran((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))\<rbrakk>\<^sub>e b \<longrightarrow> (\<lbrakk>(\<^bold>\<forall> na \<bullet> ((#\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n2\<guillemotright>) \<and> (#\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n1\<guillemotright>)))\<rbrakk>\<^sub>e b)"
      by (simp add: forall_comb')
    have n1_n2_eq: "n2 = n1"
      proof (rule ccontr)
        assume ss1: "n2 \<noteq> n1"
        have conj_false: "(\<^bold>\<forall> na \<bullet> ((#\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n2\<guillemotright>) \<and> (#\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n1\<guillemotright>))) = false"
          using ss1 apply (rel_auto)
        done
        have imp_false: "\<forall>b. \<lbrakk>Ran((pre\<^sub>D(P) \<and> post\<^sub>D(Q)))\<rbrakk>\<^sub>e b \<longrightarrow> (\<lbrakk>false\<rbrakk>\<^sub>e b)"
          using P1_Q2_implies_n2_n1_2 
          apply (simp add: "conj_false")
        done
        have dom_false: "Ran((pre\<^sub>D(P) \<and> post\<^sub>D(Q))) = false"
          by (metis imp_false true_conj_zero(2) udeduct_refineI utp_pred_laws.inf.orderE utp_pred_laws.inf_commute)
        have P1_Q2_false: "(pre\<^sub>D(P) \<and> post\<^sub>D(Q)) = false"
          by (metis assume_Ran assume_false dom_false seqr_right_zero)
        show "False"
          using s4 apply (simp add: P1_Q2_false)
        done
      qed
    show ?thesis 
      apply (simp add: n1_n2_eq m1_m2_eq)
    done
  qed

subsection {* Operators *}
subsubsection {* Id *}
lemma SimBlock_Id [simblock_healthy]:
  "SimBlock 1 1 (Id)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (simp add:  f_blocks)
  apply (metis f_Const_def length_Cons list.size(3))
  by (simp add:  f_blocks)

lemma inps_id: "inps Id = 1"
  using SimBlock_Id inps_outps by auto

lemma outps_id: "outps Id = 1"
  using SimBlock_Id inps_outps by auto

subsubsection {* Sequential Composition *}
lemma refine_seq_mono:
  assumes "P1 \<sqsubseteq> P2" and "Q1 \<sqsubseteq> Q2"
  shows "P1 ;; Q1 \<sqsubseteq> P2 ;; Q2"
  by (simp add: assms(1) assms(2) seqr_mono)

(*
lemma SimBlock_seq [simblock_healthy]:
  assumes s1: "SimBlock m1 n1 (P1 \<turnstile>\<^sub>n Q1)"
  assumes s2: "SimBlock m2 n2 (P2 \<turnstile>\<^sub>n Q2)"
  assumes s3: "out\<alpha> \<sharp> P1"
  assumes s4: "\<not> Q1 ;; (\<not> P2) \<noteq> false"
  assumes s4: "Q1 ;; Q2 \<noteq> false"
  shows "SimBlock m1 n2 ((P1 \<turnstile>\<^sub>n Q1) ;; (P2 \<turnstile>\<^sub>n Q2))"
  apply (simp add: SimBlock_def)
  apply (simp add: rdesign_composition)
  apply (rule conjI)
  proof -
    have 1: "(\<not> (\<not> P1) ;; true) = P1"
      by (metis precond_right_unit s3 seqr_true_lemma)
    then have "(\<not> (\<not> P1) ;; true) \<noteq> false"
      using s1 by (metis SimBlock_def feasibile_iff_true_right_zero rdesign_pre true_conj_zero(2) 
        utp_pred_laws.compl_eq_compl_iff utp_pred_laws.compl_top_eq)
    then show "\<not> ((\<not> (\<not> P1) ;; true \<and> \<not> Q1 ;; (\<not> P2)) \<and> Q1 ;; Q2) = false"
  
(* The inps of (P ;; Q) would not be automatically inps of P because (P ;; Q) has to satisfy 
conditions in SimBlock as well *)
lemma seq_inps:
  assumes "SimBlock m1 n1 P"
  assumes "SimBlock m2 n2 Q"
  shows "inps (P ;; Q) = inps P"

lemma seq_outps:
  shows "outps (P ;; Q) = outps Q"
  using inps_outps
  by (metis SimBlock_def impl_mp1 rdesign_post rdesign_pre utp_pred_laws.inf_top_left)
*)

lemma FBlock_seq_comp:
  assumes s1: "SimBlock m1 n1 (FBlock (\<lambda>x n. True) m1 n1 f)"
  assumes s2: "SimBlock n1 n2 (FBlock (\<lambda>x n. True) n1 n2 g)"
  shows "FBlock (\<lambda>x n. True) m1 n1 f ;; FBlock (\<lambda>x n. True) n1 n2 g = FBlock (\<lambda>x n. True) m1 n2 (g \<circ> f)"
  proof -
    show ?thesis
      apply (simp add: sim_blocks)
      apply (rel_simp)
      apply (rule iffI)
      apply (clarify)
      apply presburger
      apply (rel_auto)
      proof -
        fix ok\<^sub>v inouts\<^sub>v ok\<^sub>v' inouts\<^sub>v'
        assume a0: "ok\<^sub>v'"
        assume a1: "(\<forall>x. length(inouts\<^sub>v x) = m1 \<and> length(inouts\<^sub>v' x) = n2 \<and> 
              g (f inouts\<^sub>v) x = inouts\<^sub>v' x)"
        show "\<exists>ok\<^sub>v'' inouts\<^sub>v''.
          (ok\<^sub>v \<longrightarrow> ok\<^sub>v'' \<and> (\<forall>x. length(inouts\<^sub>v'' x) = n1 \<and> f inouts\<^sub>v x = inouts\<^sub>v'' x) 
                              \<and> (\<forall>x xa. length(x xa) = m1 \<longrightarrow> length(f x xa) = n1)) \<and>
          (ok\<^sub>v'' \<longrightarrow> (\<forall>x. length(inouts\<^sub>v'' x) = n1 \<and> g inouts\<^sub>v'' x = inouts\<^sub>v' x)
                              \<and> (\<forall>x xa. length(x xa) = n1 \<longrightarrow> length(g x xa) = n2))"
          apply (rule_tac x = "ok\<^sub>v'" in exI)
          apply (rule_tac x = "f inouts\<^sub>v" in exI, simp)
          using SimBlock_FBlock_fn a0 a1 assms(2) s1 by blast
      qed
  qed
   
lemma SimBlock_FBlock_seq_comp [simblock_healthy]:
  assumes s1: "SimBlock m1 n1 (FBlock (\<lambda>x n. True) m1 n1 f)"
  assumes s2: "SimBlock n1 n2 (FBlock (\<lambda>x n. True) n1 n2 g)"
  shows "SimBlock m1 n2 (FBlock (\<lambda>x n. True) m1 n1 f ;; FBlock (\<lambda>x n. True) n1 n2 g)"
  apply (simp add: "s1" "s2" FBlock_seq_comp)
  apply (rule SimBlock_FBlock)
  proof -
    obtain inouts\<^sub>v::"nat \<Rightarrow> real list" where P: "\<forall>na. length(inouts\<^sub>v na) = m1"
      using list_len_avail by auto
    show "\<exists>inouts\<^sub>v inouts\<^sub>v'. \<forall>x. length(inouts\<^sub>v' x) = n2 \<and> length(inouts\<^sub>v x) = m1 \<and> 
                                 (g \<circ> f) inouts\<^sub>v x = inouts\<^sub>v' x"
      apply (rule_tac x = "inouts\<^sub>v" in exI)
      apply (rule_tac x = "(g \<circ> f) inouts\<^sub>v" in exI)
      using P SimBlock_FBlock_fn assms(2) s1 by auto
  next
    show "\<forall>x na. length(x na) = m1 \<longrightarrow> length((g \<circ> f) x na) = n2"
      using SimBlock_FBlock_fn assms(2) s1 by auto
  qed

lemma FBlock_seq_comp':
  assumes s1: "SimBlock m1 n1 (FBlock (p1) m1 n1 f)"
  assumes s2: "SimBlock n1 n2 (FBlock (p2) n1 n2 g)"
  shows "FBlock (\<lambda>x n. p1 x n \<and> length(x n) = m1) m1 n1 f ;; 
         FBlock (\<lambda>x n. p2 x n \<and> length(x n) = n1) n1 n2 g 
       = FBlock (\<lambda>x n. p1 x n \<and> (p2 \<circ> f) x n \<and> length(x n) = m1) m1 n2 (g \<circ> f)"
  proof -
    from s1 have 1: "\<forall>x n. length(x n) = m1 \<longrightarrow> length(f x n) = n1"
      using SimBlock_FBlock_fn' by blast
    from s2 have 2: "\<forall>x n. length(x n) = n1 \<longrightarrow> length(g x n) = n2"
      using SimBlock_FBlock_fn' by blast
    show ?thesis
      apply (simp add: sim_blocks)
      apply (simp add: ndesign_composition_wp wp_upred_def)
      apply (rule ref_eq)
      apply (rule ndesign_refine_intro)
      apply (rel_simp)
      using "1" apply fastforce
      apply (rel_simp)
      apply (rule_tac x = "f inouts\<^sub>v" in exI)
      using "1" "2" apply simp
      apply (rule ndesign_refine_intro)
      apply (rel_simp)
      apply (metis ext)
      apply (rel_simp)
      by presburger
  qed

lemma SimBlock_FBlock_seq_comp' [simblock_healthy]:
  assumes s1: "SimBlock m1 n1 (FBlock (p1) m1 n1 f)"
  assumes s2: "SimBlock n1 n2 (FBlock (p2) n1 n2 g)"
  (* p1 and f satisfy p2 *)
  assumes s3: "\<forall>x n. (p1 x n) \<longrightarrow> (p2 o f) x n"
  shows "SimBlock m1 n2 (FBlock (\<lambda>x n. p1 x n \<and> length(x n) = m1) m1 n1 f ;; 
                         FBlock (\<lambda>x n. p2 x n \<and> length(x n) = n1) n1 n2 g)"
  apply (simp add: "s1" "s2" FBlock_seq_comp')
  apply (rule SimBlock_FBlock')
  proof -
    obtain inouts\<^sub>v::"nat \<Rightarrow> real list" where P: "\<forall>na. length(inouts\<^sub>v na) = m1 \<and> p1 inouts\<^sub>v na"
      using list_len_avail s1 SimBlock_FBlock_p by metis
    show "\<exists>inouts\<^sub>v.
       (\<forall>x. p1 inouts\<^sub>v x \<and> p2 (f inouts\<^sub>v) x \<and> length(inouts\<^sub>v x) = m1) \<and>
       (\<exists>inouts\<^sub>v'. \<forall>x. length(inouts\<^sub>v' x) = n2 \<and> length(inouts\<^sub>v x) = m1 \<and> (g \<circ> f) inouts\<^sub>v x = inouts\<^sub>v' x)"
      apply (rule_tac x = "inouts\<^sub>v" in exI)
      apply (rule conjI)
      using P s3 apply auto[1]
      apply (rule_tac x = "(g \<circ> f) inouts\<^sub>v" in exI)
      using P assms(2) SimBlock_FBlock_fn' s1 by auto
  next
    show "\<forall>x na. length(x na) = m1 \<longrightarrow> length((g \<circ> f) x na) = n2"
      using SimBlock_FBlock_fn' assms(2) s1 by auto
  qed

subsubsection {* Parallel Composition *}
paragraph {* @{text "mergeB"} *}

text {* @{text "ThreeWayMerge'"}: similar to @{text "ThreeWayMerge"}, but it merges 1 and 2 firstly 
and then merges 0. Instead, @{text "ThreeWayMerge"} merges 0 and 1 firstly, then merges 2. *}
definition ThreeWayMerge' :: "'\<alpha> merge \<Rightarrow> (('\<alpha>, '\<alpha>, ('\<alpha>, '\<alpha>, '\<alpha>) mrg) mrg, '\<alpha>) urel" ("\<^bold>M30'(_')") where
[upred_defs]: "ThreeWayMerge' M = (($0-\<^bold>v\<acute> =\<^sub>u $0-\<^bold>v \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v\<^sub><) \<and> ($0-\<^bold>v\<acute> =\<^sub>u $1-0-\<^bold>v \<and> $1-\<^bold>v\<acute> =\<^sub>u $1-1-\<^bold>v \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v\<^sub><) ;; M ;; U1) ;; M"

text {* @{text "mergeB"} is associative which means the order of merges applied to 0, 1 and 2 does 
not matter as long as 0, 1, and 2 are merged in the same order. In other word, 
  M(M(0,1), 2) = M(0, M(1, 2))
*}
lemma mergeB_assoc: "ThreeWayMerge (mergeB) = ThreeWayMerge' (mergeB)"
  apply (simp add: ThreeWayMerge_def ThreeWayMerge'_def mergeB_def)
  apply (rel_auto)
  apply (rename_tac inouts\<^sub>v0 ok\<^sub>v0 inouts\<^sub>v1 ok\<^sub>v1 inouts\<^sub>v2 ok\<^sub>v2 inouts\<^sub>v3 inouts\<^sub>v4 inouts\<^sub>v5 inouts\<^sub>v6 inouts\<^sub>v7)
  apply (rule_tac x = "(ok\<^sub>v1 \<and> ok\<^sub>v2)" in exI)
  apply (rule_tac x = "\<lambda> na. (inouts\<^sub>v2 na @ inouts\<^sub>v3 na)" in exI)
  apply (simp)
  apply (rule_tac x = "\<lambda> na. (inouts\<^sub>v2 na @ inouts\<^sub>v3 na)" in exI)
  apply (simp)
  apply (rename_tac inouts\<^sub>v0 ok\<^sub>v0 inouts\<^sub>v1 ok\<^sub>v1 inouts\<^sub>v2 ok\<^sub>v2 inouts\<^sub>v3 inouts\<^sub>v4 inouts\<^sub>v5 inouts\<^sub>v6)
  apply (rule_tac x = "inouts\<^sub>v0" in exI)
  apply (rule_tac x = "(ok\<^sub>v0 \<and> ok\<^sub>v1)" in exI)
  apply (rule_tac x = "\<lambda> na. (inouts\<^sub>v1 na @ inouts\<^sub>v2 na)" in exI)
  apply (simp)
  apply (rule_tac x = "\<lambda> na. (inouts\<^sub>v1 na @ inouts\<^sub>v2 na)" in exI)
  apply (simp)
done

paragraph {* @{text "sim_paralell"} *}

lemma SimParallel_form:
  assumes s1: "SimBlock m1 n1 B1"
  assumes s2: "SimBlock m2 n2 B2" 
  shows"(B1 \<parallel>\<^sub>B B2) = 
        (\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1, inouts\<^sub>0, inouts\<^sub>1) \<bullet> 
             (((takem (m1+m2) (m1)) ;; B1)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
             ((dropm (m1+m2) (m2)) ;; B2)\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
             (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a))) \<and>
             ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<guillemotright>))))"
    (is "?lhs = ?rhs")
  proof -
    have s3: "inps B1 = m1"
      using s1 by (simp add: inps_outps)
    have s4: "inps B2 = m2"
      using s2 by (simp add: inps_outps)
    show ?thesis
      apply (simp add: sim_parallel_def)
      apply (simp add: s3 s4 mergeB_def)
      apply (simp add: par_by_merge_alt_def, rel_auto)
      apply (rename_tac ok\<^sub>v inouts\<^sub>v' inouts\<^sub>v2 inouts\<^sub>v3 ok\<^sub>v3 inouts\<^sub>v4 ok\<^sub>v4 ok\<^sub>v5 inouts\<^sub>v5
           inouts\<^sub>v6 ok\<^sub>v6 inouts\<^sub>v7)
      apply blast
      by blast
  qed

lemma SimBlock_parallel_pre_true [simblock_healthy]:
  assumes s1: "SimBlock m1 n1 (true \<turnstile>\<^sub>n Q1)"
  assumes s2: "SimBlock m2 n2 (true \<turnstile>\<^sub>n Q2)" 
  shows "SimBlock (m1+m2) (n1+n2) ((true \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (true \<turnstile>\<^sub>n Q2))"
  proof -
    -- {* 1. Simplify the parallel operation *}
    have 1: "((true \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (true \<turnstile>\<^sub>n Q2)) = 
          (\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1, inouts\<^sub>0, inouts\<^sub>1) \<bullet> 
             (((takem (m1+m2) (m1)) ;; (true \<turnstile>\<^sub>n Q1))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
             ((dropm (m1+m2) (m2)) ;; (true \<turnstile>\<^sub>n Q2))\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
             (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a))) \<and>
             ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<guillemotright>))))"
      using SimParallel_form s1 s2 by auto
    -- {* 2. Get some basic facts from assumptions *}
    from s1 have "Q1 \<noteq> false"
      by (simp add: SimBlock_def)
    then have Q1_not_false: "\<exists>inouts\<^sub>v inouts\<^sub>v'. \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>)"
      by (rel_simp)
    from s2 have "Q2 \<noteq> false"
      by (simp add: SimBlock_def)
    then have Q2_not_false: "\<exists>inouts\<^sub>v inouts\<^sub>v'. \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>)"
      by (rel_simp)
    from s1 have "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m1\<guillemotright>) \<sqsubseteq> Dom(PrePost((true \<turnstile>\<^sub>n Q1))))"
      by (simp add: SimBlock_def)
    then have ref_m1: "\<forall>inouts\<^sub>v inouts\<^sub>v' x. \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow> length(inouts\<^sub>v x) = m1"
      by (rel_simp)
    from s2 have "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m2\<guillemotright>) \<sqsubseteq> Dom(PrePost((true \<turnstile>\<^sub>n Q2))))"
      by (simp add: SimBlock_def)
    then have ref_m2: "\<forall>inouts\<^sub>v inouts\<^sub>v' x. \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow> length(inouts\<^sub>v x) = m2"
      by (rel_simp)
    have "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n1\<guillemotright>) \<sqsubseteq> Ran(PrePost((true \<turnstile>\<^sub>n Q1))))"
      using SimBlock_def s1 by auto
    then have ref_n1: "\<forall>inouts\<^sub>v inouts\<^sub>v' x. \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>) \<longrightarrow> length(inouts\<^sub>v x) = n1"
      by (rel_simp)
    have "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n2\<guillemotright>) \<sqsubseteq> Ran(PrePost((true \<turnstile>\<^sub>n Q2))))"
      using SimBlock_def s2 by auto
    then have ref_n2: "\<forall>inouts\<^sub>v inouts\<^sub>v' x. \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>) \<longrightarrow> length(inouts\<^sub>v x) = n2"
      by (rel_simp)
    -- {* Subgoal 1 for @{text "SimBlock_def"} *}
    have c1: "PrePost((true \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (true \<turnstile>\<^sub>n Q2)) \<noteq> false"
      apply (simp add: 1)
      apply (simp add: sim_blocks)
      apply (rel_auto)
      proof - 
        obtain inouts\<^sub>v1 and inouts\<^sub>v'1 and inouts\<^sub>v2 and inouts\<^sub>v'2 
          where P1: " \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'1\<rparr>)"
          and P2: " \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'2\<rparr>)"
          using Q1_not_false Q2_not_false by blast
        show "\<exists>inouts\<^sub>v inouts\<^sub>v'.
         (\<forall>a aa ab.
             (\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                     (\<exists>inouts\<^sub>v'.
                         (\<forall>x. (m1 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m2 \<and> inouts\<^sub>v' x = []) \<and>
                              (0 < m1 \<longrightarrow>
                               length(inouts\<^sub>v x) = m1 + m2 \<and>
                               length(inouts\<^sub>v' x) = m1 \<and> take m1 (inouts\<^sub>v x) = inouts\<^sub>v' x)) \<and>
                         (ok\<^sub>v \<longrightarrow> a \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = ab\<rparr>)))) \<longrightarrow>
             (\<forall>b. (\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                          (\<exists>inouts\<^sub>v'.
                              (\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m1 \<and> inouts\<^sub>v' x = []) \<and>
                                   (0 < m2 \<longrightarrow>
                                    length(inouts\<^sub>v x) = m1 + m2 \<and>
                                    length(inouts\<^sub>v' x) = m2 \<and> drop m1 (inouts\<^sub>v x) = inouts\<^sub>v' x)) \<and>
                              (ok\<^sub>v \<longrightarrow> aa \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = b\<rparr>)))) \<longrightarrow>
                  (\<exists>x. \<not> inouts\<^sub>v' x = ab x @ b x) \<or> a \<and> aa)) \<and>
         (\<exists>a aa. (\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                         (\<exists>inouts\<^sub>v'.
                             (\<forall>x. (m1 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m2 \<and> inouts\<^sub>v' x = []) \<and>
                                  (0 < m1 \<longrightarrow>
                                   length(inouts\<^sub>v x) = m1 + m2 \<and>
                                   length(inouts\<^sub>v' x) = m1 \<and> take m1 (inouts\<^sub>v x) = inouts\<^sub>v' x)) \<and>
                             (ok\<^sub>v \<longrightarrow> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = aa\<rparr>)))) \<and>
                 (\<exists>b. (\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                              (\<exists>inouts\<^sub>v'.
                                  (\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m1 \<and> inouts\<^sub>v' x = []) \<and>
                                       (0 < m2 \<longrightarrow>
                                        length(inouts\<^sub>v x) = m1 + m2 \<and>
                                        length(inouts\<^sub>v' x) = m2 \<and> drop m1 (inouts\<^sub>v x) = inouts\<^sub>v' x)) \<and>
                                  (ok\<^sub>v \<longrightarrow> a \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = b\<rparr>)))) \<and>
                      (\<forall>x. inouts\<^sub>v' x = aa x @ b x) \<and> a))"
        apply (rule_tac x = "\<lambda>na. inouts\<^sub>v1 na @inouts\<^sub>v2 na" in exI)
        apply (rule_tac x = "\<lambda>na. inouts\<^sub>v'1 na @inouts\<^sub>v'2 na" in exI)
        apply (rule conjI)
        apply blast
        apply (rule_tac x = "True" in exI)
        apply (rule_tac x = "\<lambda>na. inouts\<^sub>v'1 na" in exI)
        apply (rule conjI)
        apply (rule_tac x = "True" in exI)
        apply (simp)
        apply (rule_tac x = "\<lambda>na. inouts\<^sub>v1 na" in exI)
        using P1 P2 ref_m1 ref_m2 apply fastforce
        apply (rule_tac x = "\<lambda>na. inouts\<^sub>v'2 na" in exI)
        apply (simp)
        apply (rule_tac x = "True" in exI)
        apply (simp)
        apply (rule_tac x = "\<lambda>na. inouts\<^sub>v2 na" in exI)
        using P1 P2 ref_m1 ref_m2 by force
    qed
    -- {* Subgoal 2 for @{text "SimBlock_def"} *}
    have c2: "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m1+m2\<guillemotright>) \<sqsubseteq> Dom(PrePost((true \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (true \<turnstile>\<^sub>n Q2))))"
      apply (simp add: 1)
      apply (simp add: sim_blocks)
      apply (rel_simp)
      using assms
      by (metis add.right_neutral not_gr_zero)
    -- {* Subgoal 3 for @{text "SimBlock_def"} *}
    have c3: "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n1+n2\<guillemotright>) \<sqsubseteq> Ran(PrePost((true \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (true \<turnstile>\<^sub>n Q2))))"
      apply (simp add: 1)
      apply (simp add: sim_blocks)
      apply (rel_simp)
      by (simp add: ref_n1 ref_n2)
    (*
    have c4: "true \<turnstile>\<^sub>n Q1 \<parallel>\<^sub>B (true \<turnstile>\<^sub>n Q2) is \<^bold>N"
      apply (simp add: "1")
      apply (simp add: Healthy_def')
      apply (rel_simp)
      apply (rule iffI)
      apply (rule_tac x = "ok\<^sub>v'" in exI)
      apply (rule_tac x = "ok\<^sub>v'" in exI)
      apply (auto)
    sorry *)
    from c1 c2 c3 show ?thesis
      apply (simp add: SimBlock_def)
    done
  qed

text {* Parallel composition of two SimBlocks (provided that the preconditions of both are condition) 
are still SimBlock. *}
lemma SimBlock_parallel [simblock_healthy]:
  assumes s1: "SimBlock m1 n1 (P1 \<turnstile>\<^sub>n Q1)"
  assumes s2: "SimBlock m2 n2 (P2 \<turnstile>\<^sub>n Q2)" 
  shows "SimBlock (m1+m2) (n1+n2) ((P1 \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>n Q2))"
proof -
  have pform: "((P1 \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>n Q2)) = 
        (\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1, inouts\<^sub>0, inouts\<^sub>1) \<bullet> 
           (((takem (m1+m2) (m1)) ;; (P1 \<turnstile>\<^sub>n Q1))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
           ((dropm (m1+m2) (m2)) ;; (P2 \<turnstile>\<^sub>n Q2))\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
           (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a))) \<and>
           ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<guillemotright>))))"
    using SimParallel_form s1 s2 by auto
  -- {* Subgoal 1 for @{text "SimBlock_def"} *}
  have c1: "PrePost((P1 \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>n Q2)) \<noteq> false"
    apply (simp add: pform)
    apply (simp add: sim_blocks)
    apply (rel_auto)
    proof -
      obtain inouts\<^sub>v1::"nat \<Rightarrow> real list" and inouts\<^sub>v'1::"nat \<Rightarrow> real list" and 
             inouts\<^sub>v2::"nat \<Rightarrow> real list" and inouts\<^sub>v'2::"nat \<Rightarrow> real list" where
        P1: "\<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>)" and
        Q1: "\<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'1\<rparr>)" and
        P2: "\<lbrakk>P2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>)" and
        Q2: "\<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'2\<rparr>)"
          using s1 s2 SimBlock_implies_not_PQ'
          by blast
      have inps1: "length(inouts\<^sub>v1 na) = m1"
          using P1 Q1 SimBlock_implies_mP s1 by blast
      have inps2: "length(inouts\<^sub>v2 na) = m2"
          using P2 Q2 SimBlock_implies_mP s2 by blast
      have outps1: "length(inouts\<^sub>v'1 na) = n1"
          using P1 Q1 SimBlock_implies_Qn s1 by blast
      have outps2: "length(inouts\<^sub>v'2 na) = n2"
          using P2 Q2 SimBlock_implies_Qn s2 by blast
      show "\<exists>inouts\<^sub>v inouts\<^sub>v'.
       (\<forall>a aa ab.
           (\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                   (\<exists>inouts\<^sub>v'.
                       (\<forall>x. (m1 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m2 \<and> inouts\<^sub>v' x = []) \<and>
                            (0 < m1 \<longrightarrow>
                             length(inouts\<^sub>v x) = m1 + m2 \<and>
                             length(inouts\<^sub>v' x) = m1 \<and> take m1 (inouts\<^sub>v x) = inouts\<^sub>v' x)) \<and>
                       (ok\<^sub>v \<and> \<lbrakk>P1\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr> \<longrightarrow>
                        a \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = ab\<rparr>)))) \<longrightarrow>
           (\<forall>b. (\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                        (\<exists>inouts\<^sub>v'.
                            (\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m1 \<and> inouts\<^sub>v' x = []) \<and>
                                 (0 < m2 \<longrightarrow>
                                  length(inouts\<^sub>v x) = m1 + m2 \<and>
                                  length(inouts\<^sub>v' x) = m2 \<and> drop m1 (inouts\<^sub>v x) = inouts\<^sub>v' x)) \<and>
                            (ok\<^sub>v \<and> \<lbrakk>P2\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr> \<longrightarrow>
                             aa \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = b\<rparr>)))) \<longrightarrow>
                (\<exists>x. \<not> inouts\<^sub>v' x = ab x @ b x) \<or> a \<and> aa)) \<and>
       (\<exists>a aa. (\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                       (\<exists>inouts\<^sub>v'.
                           (\<forall>x. (m1 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m2 \<and> inouts\<^sub>v' x = []) \<and>
                                (0 < m1 \<longrightarrow>
                                 length(inouts\<^sub>v x) = m1 + m2 \<and>
                                 length(inouts\<^sub>v' x) = m1 \<and> take m1 (inouts\<^sub>v x) = inouts\<^sub>v' x)) \<and>
                           (ok\<^sub>v \<and> \<lbrakk>P1\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr> \<longrightarrow>
                            \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = aa\<rparr>)))) \<and>
               (\<exists>b. (\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                            (\<exists>inouts\<^sub>v'.
                                (\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m1 \<and> inouts\<^sub>v' x = []) \<and>
                                     (0 < m2 \<longrightarrow>
                                      length(inouts\<^sub>v x) = m1 + m2 \<and>
                                      length(inouts\<^sub>v' x) = m2 \<and> drop m1 (inouts\<^sub>v x) = inouts\<^sub>v' x)) \<and>
                                (ok\<^sub>v \<and> \<lbrakk>P2\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr> \<longrightarrow>
                                 a \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = b\<rparr>)))) \<and>
                    (\<forall>x. inouts\<^sub>v' x = aa x @ b x) \<and> a))"
        apply (rule_tac x = "\<lambda>na . (inouts\<^sub>v1 na @inouts\<^sub>v2 na)" in exI)
        apply (rule_tac x = "\<lambda>na . (inouts\<^sub>v'1 na @inouts\<^sub>v'2 na)" in exI)
        apply (rule conjI)
        apply (rule allI)+
        apply (simp)
        apply (rule impI) 
        apply (rule allI)+
        apply (rule impI)
          proof -
            fix ok\<^sub>v1 and ok\<^sub>v2 and inouts\<^sub>v1'::"nat \<Rightarrow> real list" and inouts\<^sub>v2'::"nat \<Rightarrow> real list"
            assume a1: "\<exists>ok\<^sub>v. ok\<^sub>v \<and>
              (\<exists>inouts\<^sub>v'.
                  (\<forall>x. (m1 = 0 \<longrightarrow> length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m2 \<and> inouts\<^sub>v' x = []) \<and>
                       (0 < m1 \<longrightarrow>
                        length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 + m2 \<and>
                        length(inouts\<^sub>v' x) = m1 \<and>
                        take m1 (inouts\<^sub>v1 x) @ take (m1 - length(inouts\<^sub>v1 x)) (inouts\<^sub>v2 x) =
                        inouts\<^sub>v' x)) \<and>
                  (ok\<^sub>v \<and> \<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow>
                   ok\<^sub>v1 \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v1'\<rparr>)))"
            assume a2: "\<exists>ok\<^sub>v. ok\<^sub>v \<and>
              (\<exists>inouts\<^sub>v'.
                  (\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 \<and> inouts\<^sub>v' x = []) \<and>
                       (0 < m2 \<longrightarrow>
                        length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 + m2 \<and>
                        length(inouts\<^sub>v' x) = m2 \<and>
                        drop m1 (inouts\<^sub>v1 x) @ drop (m1 - length(inouts\<^sub>v1 x)) (inouts\<^sub>v2 x) =
                        inouts\<^sub>v' x)) \<and>
                  (ok\<^sub>v \<and> \<lbrakk>P2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow>
                   ok\<^sub>v2 \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v2'\<rparr>)))"
            from a1 have 1: "\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                (\<exists>inouts\<^sub>v'.
                  (\<forall>x. (m1 = 0 \<longrightarrow> 
                          length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m2 \<and> 
                          inouts\<^sub>v1 x = [] \<and>
                          inouts\<^sub>v' x = []) \<and>
                       (0 < m1 \<longrightarrow>
                        length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 + m2 \<and>
                        length(inouts\<^sub>v' x) = m1 \<and>
                        inouts\<^sub>v1 x = inouts\<^sub>v' x)) \<and>
                  (ok\<^sub>v \<and> \<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow>
                   ok\<^sub>v1 \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v1'\<rparr>)))"
              using inps1 P1 Q1 SimBlock_implies_mP s1
              by (smt append_take_drop_id cancel_comm_monoid_add_class.diff_cancel length_0_conv 
                length_drop take_eq_Nil)
            then have 2: "\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                (\<exists>inouts\<^sub>v'.
                  (\<forall>x. inouts\<^sub>v1 x = inouts\<^sub>v' x \<and> 
                       (m1 = 0 \<longrightarrow> 
                          length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m2 \<and>
                          inouts\<^sub>v1 x = []) \<and>
                       (0 < m1 \<longrightarrow>
                        length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 + m2 \<and>
                        length(inouts\<^sub>v1 x) = m1)) \<and>
                  (ok\<^sub>v \<and> \<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow>
                   ok\<^sub>v1 \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v1'\<rparr>)))"
              by (metis (full_types) inps1 length_0_conv length_greater_0_conv)
            then have 3: "\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                (\<exists>inouts\<^sub>v'.
                  (\<forall>x. inouts\<^sub>v1 x = inouts\<^sub>v' x) \<and>
                  (\<forall>x. (m1 = 0 \<longrightarrow> 
                          length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m2 \<and>
                          inouts\<^sub>v1 x = []) \<and>
                       (0 < m1 \<longrightarrow>
                        length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 + m2 \<and>
                        length(inouts\<^sub>v1 x) = m1)) \<and>
                  (ok\<^sub>v \<and> \<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow>
                   ok\<^sub>v1 \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v1'\<rparr>)))"
              by smt
            then have 4: "\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                (\<exists>inouts\<^sub>v'.
                  (\<forall>x. (m1 = 0 \<longrightarrow> 
                          length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m2 \<and>
                          inouts\<^sub>v1 x = []) \<and>
                       (0 < m1 \<longrightarrow>
                        length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 + m2 \<and>
                        length(inouts\<^sub>v1 x) = m1)) \<and>
                  (ok\<^sub>v \<and> \<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>) \<longrightarrow>
                   ok\<^sub>v1 \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v1'\<rparr>)))"
              by (metis "2" "3" append_Nil ext length_append less_not_refl neq0_conv)
            then have 5: "\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                  (\<forall>x. (m1 = 0 \<longrightarrow> 
                          length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m2 \<and>
                          inouts\<^sub>v1 x = []) \<and>
                       (0 < m1 \<longrightarrow>
                        length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 + m2 \<and>
                        length(inouts\<^sub>v1 x) = m1)) \<and>
                  (ok\<^sub>v \<and> \<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>) \<longrightarrow>
                   ok\<^sub>v1 \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v1'\<rparr>))"
              by (simp)
            then have 6: "
                  (\<forall>x. (m1 = 0 \<longrightarrow> 
                          length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m2 \<and>
                          inouts\<^sub>v1 x = []) \<and>
                       (0 < m1 \<longrightarrow>
                        length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 + m2 \<and>
                        length(inouts\<^sub>v1 x) = m1)) \<and>
                  (\<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>) \<longrightarrow>
                   ok\<^sub>v1 \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v1'\<rparr>))"
              by blast
            then have 7: "(\<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>) \<longrightarrow>
                   ok\<^sub>v1 \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v1'\<rparr>))"
              by simp
            from a2 have 11: "\<exists>ok\<^sub>v. ok\<^sub>v \<and>
              (\<exists>inouts\<^sub>v'.
                  (\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 \<and> 
                        inouts\<^sub>v' x = [] \<and> inouts\<^sub>v2 x = []) \<and>
                       (0 < m2 \<longrightarrow>
                        length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 + m2 \<and>
                        length(inouts\<^sub>v' x) = m2 \<and>
                        (inouts\<^sub>v2 x) = inouts\<^sub>v' x)) \<and>
                  (ok\<^sub>v \<and> \<lbrakk>P2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow>
                   ok\<^sub>v2 \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v2'\<rparr>)))"
              using inps1 P2 Q2 SimBlock_implies_mP s2
              by (smt P1 Q1 append_self_conv2 cancel_comm_monoid_add_class.diff_cancel drop_0 
                  drop_eq_Nil order_refl s1)
            then have 12: "\<exists>ok\<^sub>v. ok\<^sub>v \<and>
              (\<exists>inouts\<^sub>v'.
                  (\<forall>x. inouts\<^sub>v2 x = inouts\<^sub>v' x \<and> 
                      (m2 = 0 \<longrightarrow> length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 \<and> 
                        inouts\<^sub>v2 x = []) \<and>
                       (0 < m2 \<longrightarrow>
                        length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 + m2 \<and>
                        length(inouts\<^sub>v2 x) = m2)) \<and>
                  (ok\<^sub>v \<and> \<lbrakk>P2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow>
                   ok\<^sub>v2 \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v2'\<rparr>)))"
              by (metis (full_types) inps2 length_0_conv length_greater_0_conv)
            then have 13: "\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                (\<exists>inouts\<^sub>v'.
                  (\<forall>x. inouts\<^sub>v2 x = inouts\<^sub>v' x) \<and>
                  (\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 \<and> 
                        inouts\<^sub>v2 x = []) \<and>
                       (0 < m2 \<longrightarrow>
                        length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 + m2 \<and>
                        length(inouts\<^sub>v2 x) = m2)) \<and>
                  (ok\<^sub>v \<and> \<lbrakk>P2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow>
                   ok\<^sub>v2 \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v2'\<rparr>)))"
              by smt
            then have 14: "\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                (\<exists>inouts\<^sub>v'.
                  (\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 \<and> 
                        inouts\<^sub>v2 x = []) \<and>
                       (0 < m2 \<longrightarrow>
                        length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 + m2 \<and>
                        length(inouts\<^sub>v2 x) = m2)) \<and>
                  (ok\<^sub>v \<and> \<lbrakk>P2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>) \<longrightarrow>
                   ok\<^sub>v2 \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v2'\<rparr>)))"
              by (metis "12" "13" append_Nil ext length_append less_not_refl neq0_conv)
            then have 15: "\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                  (\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 \<and> 
                        inouts\<^sub>v2 x = []) \<and>
                       (0 < m2 \<longrightarrow>
                        length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 + m2 \<and>
                        length(inouts\<^sub>v2 x) = m2)) \<and>
                  (ok\<^sub>v \<and> \<lbrakk>P2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>) \<longrightarrow>
                   ok\<^sub>v2 \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v2'\<rparr>))"
              by (simp)
            then have 16: "
                  (\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 \<and> 
                        inouts\<^sub>v2 x = []) \<and>
                       (0 < m2 \<longrightarrow>
                        length(inouts\<^sub>v1 x) + length(inouts\<^sub>v2 x) = m1 + m2 \<and>
                        length(inouts\<^sub>v2 x) = m2)) \<and>
                  ( \<lbrakk>P2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>) \<longrightarrow>
                   ok\<^sub>v2 \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v2'\<rparr>))"
              by blast
            then have 17: "( \<lbrakk>P2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>) \<longrightarrow>
                   ok\<^sub>v2 \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v2'\<rparr>))"
              by simp
            show "(\<exists>x. \<not> inouts\<^sub>v'1 x @ inouts\<^sub>v'2 x = inouts\<^sub>v1' x @ inouts\<^sub>v2' x) \<or> ok\<^sub>v1 \<and> ok\<^sub>v2"
              proof (rule ccontr)
                assume aa: "\<not> ((\<exists>x. \<not> inouts\<^sub>v'1 x @ inouts\<^sub>v'2 x = inouts\<^sub>v1' x @ inouts\<^sub>v2' x) \<or> ok\<^sub>v1 \<and> ok\<^sub>v2)"
                from aa have b1: "(\<forall>x. inouts\<^sub>v'1 x @ inouts\<^sub>v'2 x = inouts\<^sub>v1' x @ inouts\<^sub>v2' x) \<and> (\<not> ok\<^sub>v1 \<or> \<not> ok\<^sub>v2)"
                  by (simp)
                from b1 have b2: "(\<forall>x. inouts\<^sub>v'1 x @ inouts\<^sub>v'2 x = inouts\<^sub>v1' x @ inouts\<^sub>v2' x)"
                  by (simp)
                from b1 have b3: "(\<not> ok\<^sub>v1 \<or> \<not> ok\<^sub>v2)"
                  by (simp)
                from b3 7 17 have b4: 
                     "\<not> \<lbrakk>P2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>) \<or> 
                      \<not> \<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>)"
                  by blast
                from s1 have b5: "\<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>)" 
                  using P1 SimBlock_implies_not_P_cond 
                  by blast
                from s2 have b6: "\<lbrakk>P2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>)" 
                  using P2 SimBlock_implies_not_P_cond by blast
                show False
                  using b4 b5 b6 by (auto)
              qed
          next
            show "\<exists>a aa. (\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                   (\<exists>inouts\<^sub>v'.
                       (\<forall>x. (m1 = 0 \<longrightarrow> length(inouts\<^sub>v1 x @ inouts\<^sub>v2 x) = m2 \<and> inouts\<^sub>v' x = []) \<and>
                            (0 < m1 \<longrightarrow>
                             length(inouts\<^sub>v1 x @ inouts\<^sub>v2 x) = m1 + m2 \<and>
                             length(inouts\<^sub>v' x) = m1 \<and> take m1 (inouts\<^sub>v1 x @ inouts\<^sub>v2 x) = inouts\<^sub>v' x)) \<and>
                       (ok\<^sub>v \<and> \<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow>
                        \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = aa\<rparr>)))) \<and>
                (\<exists>b. (\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                   (\<exists>inouts\<^sub>v'.
                       (\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v1 x @ inouts\<^sub>v2 x) = m1 \<and> inouts\<^sub>v' x = []) \<and>
                           (0 < m2 \<longrightarrow>
                            length(inouts\<^sub>v1 x @ inouts\<^sub>v2 x) = m1 + m2 \<and>
                            length(inouts\<^sub>v' x) = m2 \<and> drop m1 (inouts\<^sub>v1 x @ inouts\<^sub>v2 x) = inouts\<^sub>v' x)) \<and>
                      (ok\<^sub>v \<and> \<lbrakk>P2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow>
                       a \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>, \<lparr>inouts\<^sub>v = b\<rparr>)))) \<and>
                (\<forall>x. inouts\<^sub>v'1 x @ inouts\<^sub>v'2 x = aa x @ b x) \<and> a)"
              apply (rule_tac x = "True" in exI)
              apply (rule_tac x = "inouts\<^sub>v'1" in exI)
              apply (rule conjI)
              apply (rule_tac x = "True" in exI, simp)
              apply (rule_tac x = "inouts\<^sub>v1" in exI)
              using P1 P2 Q1 Q2 SimBlock_implies_mP s1 s2
              apply (smt add_eq_self_zero append.right_neutral 
                cancel_ab_semigroup_add_class.add_diff_cancel_left' order_refl sum_eq_sum_conv 
                take_all take_eq_Nil)
              apply (rule_tac x = "inouts\<^sub>v'2" in exI, simp)
              apply (rule_tac x = "True" in exI, simp)
              apply (rule_tac x = "inouts\<^sub>v2" in exI)
              using P1 P2 Q1 Q2 SimBlock_implies_mP s1 s2 
              by (smt add_eq_self_zero append_eq_append_conv_if 
                cancel_ab_semigroup_add_class.add_diff_cancel_left' drop_0 list_exhaust_size_eq0 
                sum_eq_sum_conv)
          qed
    qed
  -- {* Subgoal 2 for @{text "SimBlock_def"} *}
  have c2: "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m1+m2\<guillemotright>) \<sqsubseteq> Dom(PrePost((P1 \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>n Q2))))"
    apply (simp add: pform)
    apply (simp add: sim_blocks)
    apply (rel_simp)
    using assms
    by (metis add.right_neutral not_gr_zero)
  -- {* Subgoal 3 for @{text "SimBlock_def"} *}
  have c3: "((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n1+n2\<guillemotright>) \<sqsubseteq> Ran(PrePost((P1 \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>n Q2))))"
    apply (simp add: pform)
    apply (simp add: sim_blocks)
    apply (rel_simp)
    apply (rename_tac inouts\<^sub>v' inouts\<^sub>v n ok\<^sub>vq1 ok\<^sub>vq2 inouts\<^sub>v1' ok\<^sub>v inouts\<^sub>v2' inouts\<^sub>v1 ok\<^sub>v' inouts\<^sub>v2)
    proof -
      fix inouts\<^sub>v' inouts\<^sub>v n ok\<^sub>vq1 ok\<^sub>vq2 inouts\<^sub>v1' ok\<^sub>v inouts\<^sub>v2' inouts\<^sub>v1 ok\<^sub>v' inouts\<^sub>v2
      assume a1: "\<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>) \<longrightarrow> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v1'\<rparr>)"
      assume a2: "\<lbrakk>P2\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr> \<longrightarrow> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v2'\<rparr>)"
      assume a3: "\<forall>a aa ab.
          (\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                  (\<exists>inouts\<^sub>v.
                      (\<forall>x. (m1 = 0 \<longrightarrow> inouts\<^sub>v x = []) \<and>
                           (0 < m1 \<longrightarrow> length(inouts\<^sub>v x) = m1 \<and> inouts\<^sub>v1 x = inouts\<^sub>v x)) \<and>
                      (ok\<^sub>v \<and> \<lbrakk>P1\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr> \<longrightarrow>
                       a \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = ab\<rparr>)))) \<longrightarrow>
          (\<forall>b. (\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                       (\<exists>inouts\<^sub>v.
                           (\<forall>x. (m2 = 0 \<longrightarrow> inouts\<^sub>v x = []) \<and>
                                (0 < m2 \<longrightarrow> length(inouts\<^sub>v x) = m2 \<and> inouts\<^sub>v2 x = inouts\<^sub>v x)) \<and>
                           (ok\<^sub>v \<and> \<lbrakk>P2\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr> \<longrightarrow>
                            aa \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = b\<rparr>)))) \<longrightarrow>
               (\<exists>x. \<not> inouts\<^sub>v1' x @ inouts\<^sub>v2' x = ab x @ b x) \<or> a \<and> aa)"
      assume a4: "\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v1' x @ inouts\<^sub>v2' x"
      assume a5: " \<forall>x. (m1 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m2 \<and> inouts\<^sub>v1 x = []) \<and>
           (0 < m1 \<longrightarrow> length(inouts\<^sub>v x) = m1 + m2 \<and> length(inouts\<^sub>v1 x) = m1 \<and> 
                      take m1 (inouts\<^sub>v x) = inouts\<^sub>v1 x)"
      assume a6: "\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m1 \<and> inouts\<^sub>v2 x = []) \<and>
           (0 < m2 \<longrightarrow> length(inouts\<^sub>v x) = m1 + m2 \<and> length(inouts\<^sub>v2 x) = m2 \<and> 
                      drop m1 (inouts\<^sub>v x) = inouts\<^sub>v2 x)"
      from a5 have 1: "length(inouts\<^sub>v1 na) = m1"
        by blast
      from a6 have 2: "length(inouts\<^sub>v2 na) = m2"
        by blast
      from a3 have "(\<forall>a aa ab.
          (\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                  (\<exists>inouts\<^sub>v.
                      (\<forall>x. (m1 = 0 \<longrightarrow> inouts\<^sub>v x = []) \<and>
                           (0 < m1 \<longrightarrow> length(inouts\<^sub>v x) = m1 \<and> inouts\<^sub>v1 x = inouts\<^sub>v x)) \<and>
                      (ok\<^sub>v \<and> \<lbrakk>P1\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr> \<longrightarrow>
                       a \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = ab\<rparr>)))) \<longrightarrow>
          (\<forall>b. (\<exists>ok\<^sub>v. ok\<^sub>v \<and>
                       (\<exists>inouts\<^sub>v.
                           (\<forall>x. (m2 = 0 \<longrightarrow> inouts\<^sub>v x = []) \<and>
                                (0 < m2 \<longrightarrow> length(inouts\<^sub>v x) = m2 \<and> inouts\<^sub>v2 x = inouts\<^sub>v x)) \<and>
                           (ok\<^sub>v \<and> \<lbrakk>P2\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr> \<longrightarrow>
                            aa \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = b\<rparr>)))) \<longrightarrow>
               (\<exists>x. \<not> inouts\<^sub>v1' x @ inouts\<^sub>v2' x = ab x @ b x) \<or> a \<and> aa)) 
        \<longrightarrow> (\<forall>a aa ab.
          (\<lbrakk>P1\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr> \<longrightarrow>
                       a \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>, \<lparr>inouts\<^sub>v = ab\<rparr>)) \<longrightarrow>
          (\<forall>b. (\<lbrakk>P2\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr> \<longrightarrow>
                       aa \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>, \<lparr>inouts\<^sub>v = b\<rparr>)) \<longrightarrow>
               (\<exists>x. \<not> inouts\<^sub>v1' x @ inouts\<^sub>v2' x = ab x @ b x) \<or> a \<and> aa))"
        apply (simp)
        apply (rule allI)+
        apply (rename_tac ok\<^sub>vq inouts\<^sub>v1'q inouts\<^sub>v2'q)
        apply (rule impI)
        apply (rule allI)
        apply (rule impI)
        by (smt a5 a6 neq0_conv)
      then have a3': "(\<forall>a aa ab.
          (\<lbrakk>P1\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr> \<longrightarrow>
                       a \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>, \<lparr>inouts\<^sub>v = ab\<rparr>)) \<longrightarrow>
          (\<forall>b. (\<lbrakk>P2\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr> \<longrightarrow>
                       aa \<and> \<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>, \<lparr>inouts\<^sub>v = b\<rparr>)) \<longrightarrow>
               (\<exists>x. \<not> inouts\<^sub>v1' x @ inouts\<^sub>v2' x = ab x @ b x) \<or> a \<and> aa))"
        using a3 by smt
      have P1: "\<lbrakk>P1\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>" 
        using a3' using a2 by blast
      then have Q1: "\<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v1\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v1'\<rparr>)"
        using a1 by auto
      then have N1: "length(inouts\<^sub>v1' n) = n1"
        using P1 SimBlock_implies_Qn s1 by blast
      have P2: "\<lbrakk>P2\<rbrakk>\<^sub>e \<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>" 
        using a3' using a1 by blast
      then have Q2: "\<lbrakk>Q2\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v2\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v2'\<rparr>)"
        using a2 by auto
      then have N2: "length(inouts\<^sub>v2' n) = n2"
        using P2 SimBlock_implies_Qn s2 by blast
      show "length(inouts\<^sub>v1' n) + length(inouts\<^sub>v2' n) = n1 + n2"
        using N1 N2 by auto
    qed
  from c1 c2 c3 show ?thesis
    apply (simp add: SimBlock_def)
  done
qed

lemma inps_parallel:
  assumes s1: "SimBlock m1 n1 (P1 \<turnstile>\<^sub>n Q1)"
  assumes s2: "SimBlock m2 n2 (P2 \<turnstile>\<^sub>n Q2)" 
  shows "inps ((P1 \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>n Q2)) = m1 + m2"
  using SimBlock_parallel inps_outps s1 s2 by blast

lemma outps_parallel:
  assumes s1: "SimBlock m1 n1 (P1 \<turnstile>\<^sub>n Q1)"
  assumes s2: "SimBlock m2 n2 (P2 \<turnstile>\<^sub>n Q2)" 
  shows "outps ((P1 \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>n Q2)) = n1 + n2"
    using SimBlock_parallel inps_outps 
    using s1 s2 by blast

text {* Associativity of parallel composition. *}
lemma parallel_ass:
  assumes s1: "SimBlock m0 n0 (P0 \<turnstile>\<^sub>n Q0)"
  assumes s2: "SimBlock m1 n1 (P1 \<turnstile>\<^sub>n Q1)" 
  assumes s3: "SimBlock m2 n2 (P2 \<turnstile>\<^sub>n Q2)"
  shows "((P0 \<turnstile>\<^sub>n Q0) \<parallel>\<^sub>B ((P1 \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>n Q2))) = (((P0 \<turnstile>\<^sub>n Q0) \<parallel>\<^sub>B (P1 \<turnstile>\<^sub>n Q1)) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>n Q2))"
    (is "?lhs = ?rhs")
  proof -
    let ?P12 = "\<^bold>\<exists> (ok\<^sub>1, ok\<^sub>2, inouts\<^sub>1, inouts\<^sub>2) \<bullet> 
           (((takem (m1+m2) (m1)) ;; (P1 \<turnstile>\<^sub>n Q1))\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
           ((dropm (m1+m2) (m2)) ;; (P2 \<turnstile>\<^sub>n Q2))\<lbrakk>\<guillemotleft>ok\<^sub>2\<guillemotright>,\<guillemotleft>inouts\<^sub>2\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
           (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>2 n\<guillemotright>)\<^sub>a))) \<and>
           ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>1\<guillemotright> \<and> \<guillemotleft>ok\<^sub>2\<guillemotright>)))"
    have lhs_12: "((P1 \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>n Q2)) = ?P12"
      using SimParallel_form s2 s3 by blast
    have lhs_12_sim: "SimBlock (m1+m2) (n1+n2) ((P1 \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>n Q2))"
      by (simp add: SimBlock_parallel s2 s3)
    then have lhs_sim: "?lhs = 
          (\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1\<^sub>2, inouts\<^sub>0, inouts\<^sub>1\<^sub>2) \<bullet> 
             (((takem (m0+(m1+m2)) (m0)) ;; (P0 \<turnstile>\<^sub>n Q0))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
             ((dropm (m0+(m1+m2)) (m1+m2)) ;; ?P12)\<lbrakk>\<guillemotleft>ok\<^sub>1\<^sub>2\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<^sub>2\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
             (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1\<^sub>2 n\<guillemotright>)\<^sub>a))) \<and>
             ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<^sub>2\<guillemotright>))))"
      using lhs_12_sim lhs_12 SimParallel_form s1 s2 s3 by auto

    let ?P01 = "\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1, inouts\<^sub>0, inouts\<^sub>1) \<bullet> 
           (((takem (m0+m1) (m0)) ;; (P0 \<turnstile>\<^sub>n Q0))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
           ((dropm (m0+m1) (m1)) ;; (P1 \<turnstile>\<^sub>n Q1))\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
           (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a))) \<and>
           ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<guillemotright>)))"
    have rhs_01: "((P0 \<turnstile>\<^sub>n Q0) \<parallel>\<^sub>B (P1 \<turnstile>\<^sub>n Q1)) = ?P01"
      using SimParallel_form s1 s2 by blast
    have rhs_01_sim: "SimBlock (m0+m1) (n0+n1) ((P0 \<turnstile>\<^sub>n Q0) \<parallel>\<^sub>B (P1 \<turnstile>\<^sub>n Q1))"
      by (simp add: SimBlock_parallel s1 s2)
    then have rhs_sim: "?rhs = 
          (\<^bold>\<exists> (ok\<^sub>0\<^sub>1, ok\<^sub>2, inouts\<^sub>0\<^sub>1, inouts\<^sub>2) \<bullet> 
             (((takem ((m0+m1)+m2) (m0+m1)) ;; ?P01)\<lbrakk>\<guillemotleft>ok\<^sub>0\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
             ((dropm ((m0+m1)+m2) (m2)) ;; (P2 \<turnstile>\<^sub>n Q2))\<lbrakk>\<guillemotleft>ok\<^sub>2\<guillemotright>,\<guillemotleft>inouts\<^sub>2\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
             (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0\<^sub>1 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>2 n\<guillemotright>)\<^sub>a))) \<and>
             ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<^sub>1\<guillemotright> \<and> \<guillemotleft>ok\<^sub>2\<guillemotright>))))"
      using rhs_01_sim rhs_01 SimParallel_form s1 s2 s3 by auto
    show ?thesis
      apply (simp add: lhs_sim rhs_sim)
      apply (simp add: sim_blocks)
      apply (rel_simp)
      apply (rule iffI)
      -- {* Subgoal 1: lhs --> rhs *}
      apply (clarify)
      apply (rename_tac ok\<^sub>v inouts\<^sub>v ok\<^sub>v' inouts\<^sub>v' ok\<^sub>v'q0 aa inouts\<^sub>v'q0 ok\<^sub>vp0 inouts\<^sub>v'12  inouts\<^sub>vp0 ok\<^sub>v12
        inouts\<^sub>v12 ok\<^sub>v'q1 ok\<^sub>v'q2 inouts\<^sub>v'q1 ok\<^sub>vp1 inouts\<^sub>v'q2 inouts\<^sub>vp1 ok\<^sub>vp2 inouts\<^sub>vp2)
      apply (rule_tac x = "ok\<^sub>v'q0 \<and> ok\<^sub>v'q1" in exI)
      apply (rule_tac x = "ok\<^sub>v'q2" in exI)
      apply (rule_tac x = "\<lambda>na. (inouts\<^sub>v'q0 na @ inouts\<^sub>v'q1 na)" in exI)
      apply (rule conjI)
      apply (rule_tac x = "ok\<^sub>v" in exI)
      apply (rule_tac x = "\<lambda>na. (inouts\<^sub>vp0 na @ inouts\<^sub>vp1 na)" in exI)
      apply (rule conjI)
      apply (clarify)
      apply (smt ab_semigroup_add_class.add_ac(1) drop_0 gr0I length_append list.size(3) 
        self_append_conv take_add)
      apply (rule_tac x = "ok\<^sub>v'q0" in exI)
      apply (rule_tac x = "ok\<^sub>v'q1" in exI)
      apply (rule_tac x = "inouts\<^sub>v'q0" in exI)
      apply (rule conjI)
      apply (rule_tac x = "ok\<^sub>vp0" in exI)
      apply (rule_tac x = "inouts\<^sub>vp0" in exI)
      apply (rule conjI, simp)
      apply (metis gr0I length_0_conv)
      apply blast
      apply (rule_tac x = "inouts\<^sub>v'q1" in exI)
      apply (rule conjI)
      apply (rule_tac x = "ok\<^sub>vp1" in exI)
      apply (rule_tac x = "inouts\<^sub>vp1" in exI)
      apply (rule conjI, simp)
      apply (metis append_eq_conv_conj drop_append list.size(3) neq0_conv)
      apply blast
      apply blast
      apply (rule_tac x = "inouts\<^sub>v'q2" in exI)
      apply (rule conjI, simp)
      apply (rule_tac x = "ok\<^sub>vp2" in exI)
      apply (rule_tac x = "inouts\<^sub>vp2" in exI)
      apply (rule conjI, simp)
      apply (metis add_cancel_left_right drop_drop gr0I semiring_normalization_rules(24))
      apply blast
      apply auto[1]
      -- {* Subgoal 2: rhs --> lhs *}
      apply (clarify)
      apply (rename_tac ok\<^sub>v inouts\<^sub>v ok\<^sub>v' inouts\<^sub>v' a ok\<^sub>v'q2 inouts\<^sub>v'01 ok\<^sub>v01 inouts\<^sub>v'q2 inouts\<^sub>v01 ok\<^sub>vp2 inouts\<^sub>vp2 
        ok\<^sub>v'q0 ok\<^sub>v'q1 inouts\<^sub>v'q0 ok\<^sub>vp0 inouts\<^sub>v'q1 inouts\<^sub>vp0 ok\<^sub>vp1 inouts\<^sub>vp1)
      apply (rule_tac x = "ok\<^sub>v'q0" in exI)
      apply (rule_tac x = "ok\<^sub>v'q1 \<and> ok\<^sub>v'q2" in exI)
      apply (rule_tac x = "\<lambda>na. (inouts\<^sub>v'q0 na)" in exI)
      apply (rule conjI)
      apply (rule_tac x = "ok\<^sub>v" in exI)
      apply (rule_tac x = "\<lambda>na. (inouts\<^sub>vp0 na)" in exI)
      apply (rule conjI, simp)
      apply (rule impI)
      apply (rule allI)
      apply (rule conjI)
      apply (metis add_cancel_left_left zero_less_iff_neq_zero)
      apply (metis append.right_neutral append_take_drop_id diff_is_0_eq le_add1 take_0 take_append)
      apply blast
      apply (rule_tac x = "\<lambda>na. (inouts\<^sub>v'q1 na @ inouts\<^sub>v'q2 na)" in exI)
      apply (rule conjI)
      apply (rule_tac x = "ok\<^sub>v" in exI)
      apply (rule_tac x = "\<lambda>na. (inouts\<^sub>vp1 na @ inouts\<^sub>vp2 na)" in exI)
      apply (rule conjI, simp)
      apply (rule impI)
      apply (rule allI)
      apply (rule conjI)
      apply (smt add.commute append_take_drop_id drop_drop length_append length_greater_0_conv 
        less_add_same_cancel2 neq0_conv take_drop)
      apply (rule impI)
      apply (rule conjI)
      apply (metis gr_zeroI list.size(3))
      apply (metis (no_types, hide_lams) add.left_neutral append_take_drop_id diff_add_zero drop_0 
        drop_append neq0_conv plus_list_def zero_list_def)
      apply (rule_tac x = "ok\<^sub>v'q1" in exI)
      apply (rule_tac x = "ok\<^sub>v'q2" in exI)
      apply (rule_tac x = "inouts\<^sub>v'q1" in exI)
      apply (rule conjI, simp)
      apply (metis gr0I length_0_conv)
      apply (rule_tac x = "inouts\<^sub>v'q2" in exI)
      apply (rule conjI)
      apply (rule_tac x = "ok\<^sub>vp2" in exI)
      apply (rule_tac x = "inouts\<^sub>vp2" in exI)
      apply (rule conjI, simp)
      apply (metis append_eq_conv_conj drop_append list.size(3) neq0_conv)
      apply blast
      apply blast
      apply (rule conjI, simp)
      by blast
  qed
(*
lemma parallel_ass:
  assumes s1: "SimBlock m0 n0 ((FBlock (\<lambda>x n. True) m0 n0 f))"
  assumes s2: "SimBlock m1 n1 ((FBlock (\<lambda>x n. True) m1 n1 g))" 
  assumes s3: "SimBlock m2 n2 ((FBlock (\<lambda>x n. True) m2 n2 h))"
  shows "((((FBlock (\<lambda>x n. True) m0 n0 f)) \<parallel>\<^sub>B ((FBlock (\<lambda>x n. True) m1 n1 g))) \<parallel>\<^sub>B ((FBlock (\<lambda>x n. True) m2 n2 h))) 
    = (((FBlock (\<lambda>x n. True) m0 n0 f)) \<parallel>\<^sub>B (((FBlock (\<lambda>x n. True) m1 n1 g)) \<parallel>\<^sub>B ((FBlock (\<lambda>x n. True) m2 n2 h))))"
    (is "?lhs = ?rhs")
  apply (simp add: FBlock_def)
  proof -
    have "SimBlock m0 n0 (true \<turnstile>\<^sub>n
      ((\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m0\<guillemotright> \<and> #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n0\<guillemotright> \<and> \<guillemotleft>f\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u $inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) \<and>
       (\<^bold>\<forall> x \<bullet> \<^bold>\<forall> n \<bullet> #\<^sub>u(\<guillemotleft>f x n\<guillemotright>) =\<^sub>u \<guillemotleft>n0\<guillemotright>)))"
      using s1 apply (simp add: FBlock_def)
*)

lemma refinement_implies_r:
  assumes s1: "(P1 \<turnstile>\<^sub>r Q1) \<sqsubseteq> (P1r \<turnstile>\<^sub>r Q1r)"
  shows "\<forall>ok\<^sub>v inouts\<^sub>v ok\<^sub>v' inouts\<^sub>v'.
          (ok\<^sub>v \<and> \<lbrakk>P1r\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow>
           ok\<^sub>v' \<and> \<lbrakk>Q1r\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>)) \<longrightarrow>
          (ok\<^sub>v \<and> \<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>) \<longrightarrow>
          ok\<^sub>v' \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>))"
  using s1 apply (rel_simp)
  by blast

lemma refinement_implies:
  assumes s1: "(P1 \<turnstile>\<^sub>n Q1) \<sqsubseteq> (P1r \<turnstile>\<^sub>n Q1r)"
  shows "\<forall>ok\<^sub>v inouts\<^sub>v ok\<^sub>v' inouts\<^sub>v'.
          (ok\<^sub>v \<and> \<lbrakk>P1r\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>) \<longrightarrow>
           ok\<^sub>v' \<and> \<lbrakk>Q1r\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>)) \<longrightarrow>
          (ok\<^sub>v \<and> \<lbrakk>P1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>) \<longrightarrow>
          ok\<^sub>v' \<and> \<lbrakk>Q1\<rbrakk>\<^sub>e (\<lparr>inouts\<^sub>v = inouts\<^sub>v\<rparr>, \<lparr>inouts\<^sub>v = inouts\<^sub>v'\<rparr>))"
  using s1 apply (rel_simp)
  by blast

lemma parallel_mono_r:
  assumes s1: "SimBlock m1 n1 (P1 \<turnstile>\<^sub>r Q1)"
  assumes s2: "SimBlock m2 n2 (P2 \<turnstile>\<^sub>r Q2)" 
  assumes s3: "SimBlock m1 n1 (P1r \<turnstile>\<^sub>r Q1r)"
  assumes s4: "SimBlock m2 n2 (P2r \<turnstile>\<^sub>r Q2r)"
  assumes s5: "(P1 \<turnstile>\<^sub>r Q1) \<sqsubseteq> (P1r \<turnstile>\<^sub>r Q1r)" 
  assumes s6: "(P2 \<turnstile>\<^sub>r Q2) \<sqsubseteq> (P2r \<turnstile>\<^sub>r Q2r)"
  shows "((P1 \<turnstile>\<^sub>r Q1) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>r Q2)) \<sqsubseteq> ((P1r \<turnstile>\<^sub>r Q1r) \<parallel>\<^sub>B (P2r \<turnstile>\<^sub>r Q2r))"
  proof -
    have pform: "((P1 \<turnstile>\<^sub>r Q1) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>r Q2)) = 
      (\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1, inouts\<^sub>0, inouts\<^sub>1) \<bullet> 
         (((takem (m1+m2) (m1)) ;; (P1 \<turnstile>\<^sub>r Q1))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
         ((dropm (m1+m2) (m2)) ;; (P2 \<turnstile>\<^sub>r Q2))\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
         (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a))) \<and>
         ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<guillemotright>))))"
      using SimParallel_form s1 s2 by auto
    have pform': "((P1r \<turnstile>\<^sub>r Q1r) \<parallel>\<^sub>B (P2r \<turnstile>\<^sub>r Q2r)) = 
      (\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1, inouts\<^sub>0, inouts\<^sub>1) \<bullet> 
         (((takem (m1+m2) (m1)) ;; (P1r \<turnstile>\<^sub>r Q1r))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
         ((dropm (m1+m2) (m2)) ;; (P2r \<turnstile>\<^sub>r Q2r))\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
         (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a))) \<and>
         ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<guillemotright>))))"
      using SimParallel_form s3 s4 by auto
    show ?thesis
      apply (simp add: pform pform')
      apply (simp add: sim_blocks)
      apply (rel_simp)
      apply (rename_tac ok\<^sub>v inouts\<^sub>v inouts\<^sub>v' ok\<^sub>vq1r ok\<^sub>vq2r inouts\<^sub>v1r' ok\<^sub>vp1r inouts\<^sub>v2r' inouts\<^sub>v1r ok\<^sub>vp2r inouts\<^sub>v2r)
      apply (rule_tac x = "ok\<^sub>vq1r" in exI)
      apply (rule_tac x = "ok\<^sub>vq2r" in exI)
      apply (rule_tac x = "inouts\<^sub>v1r'" in exI)
      apply (simp)
      apply (rule conjI)
      apply (rule_tac x = "ok\<^sub>vp1r" in exI, simp)
      apply (rule_tac x = "inouts\<^sub>v1r" in exI)
      apply (rule conjI)
      apply simp
      using s5 s1 refinement_implies_r apply (metis)
      apply (rule_tac x = "inouts\<^sub>v2r'" in exI, simp)
      apply (rule_tac x = "ok\<^sub>vp2r" in exI)
      apply simp
      apply (rule_tac x = "inouts\<^sub>v2r" in exI, simp)
      using s6 s2 refinement_implies_r apply (metis)
    done
  qed

lemma parallel_mono:
  assumes s1: "SimBlock m1 n1 (P1 \<turnstile>\<^sub>n Q1)"
  assumes s2: "SimBlock m2 n2 (P2 \<turnstile>\<^sub>n Q2)" 
  assumes s3: "SimBlock m1 n1 (P1r \<turnstile>\<^sub>n Q1r)"
  assumes s4: "SimBlock m2 n2 (P2r \<turnstile>\<^sub>n Q2r)"
  assumes s5: "(P1 \<turnstile>\<^sub>n Q1) \<sqsubseteq> (P1r \<turnstile>\<^sub>n Q1r)" 
  assumes s6: "(P2 \<turnstile>\<^sub>n Q2) \<sqsubseteq> (P2r \<turnstile>\<^sub>n Q2r)"
  shows "((P1 \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>n Q2)) \<sqsubseteq> ((P1r \<turnstile>\<^sub>n Q1r) \<parallel>\<^sub>B (P2r \<turnstile>\<^sub>n Q2r))"
  proof -
    have pform: "((P1 \<turnstile>\<^sub>n Q1) \<parallel>\<^sub>B (P2 \<turnstile>\<^sub>n Q2)) = 
      (\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1, inouts\<^sub>0, inouts\<^sub>1) \<bullet> 
         (((takem (m1+m2) (m1)) ;; (P1 \<turnstile>\<^sub>n Q1))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
         ((dropm (m1+m2) (m2)) ;; (P2 \<turnstile>\<^sub>n Q2))\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
         (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a))) \<and>
         ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<guillemotright>))))"
      using SimParallel_form s1 s2 by auto
    have pform': "((P1r \<turnstile>\<^sub>n Q1r) \<parallel>\<^sub>B (P2r \<turnstile>\<^sub>n Q2r)) = 
      (\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1, inouts\<^sub>0, inouts\<^sub>1) \<bullet> 
         (((takem (m1+m2) (m1)) ;; (P1r \<turnstile>\<^sub>n Q1r))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
         ((dropm (m1+m2) (m2)) ;; (P2r \<turnstile>\<^sub>n Q2r))\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
         (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a))) \<and>
         ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<guillemotright>))))"
      using SimParallel_form s3 s4 by auto
    show ?thesis
      apply (simp add: pform pform')
      apply (simp add: sim_blocks)
      apply (rel_simp)
      apply (rename_tac ok\<^sub>v inouts\<^sub>v inouts\<^sub>v' ok\<^sub>vq1r ok\<^sub>vq2r inouts\<^sub>v1r' ok\<^sub>vp1r inouts\<^sub>v2r' inouts\<^sub>v1r ok\<^sub>vp2r inouts\<^sub>v2r)
      apply (rule_tac x = "ok\<^sub>vq1r" in exI)
      apply (rule_tac x = "ok\<^sub>vq2r" in exI)
      apply (rule_tac x = "inouts\<^sub>v1r'" in exI)
      apply (simp)
      apply (rule conjI)
      apply (rule_tac x = "ok\<^sub>vp1r" in exI, simp)
      apply (rule_tac x = "inouts\<^sub>v1r" in exI)
      apply (rule conjI)
      apply simp
      using s5 s1 refinement_implies apply (metis)
      apply (rule_tac x = "inouts\<^sub>v2r'" in exI, simp)
      apply (rule_tac x = "ok\<^sub>vp2r" in exI)
      apply simp
      apply (rule_tac x = "inouts\<^sub>v2r" in exI, simp)
      using s6 s2 refinement_implies apply (metis)
    done
  qed
  
lemma FBlock_parallel_comp_id:
  assumes s1: "SimBlock 1 1 (FBlock (\<lambda>x n. True) 1 1 f_Id)"
  shows "(FBlock (\<lambda>x n. True) 1 1 f_Id) \<parallel>\<^sub>B (FBlock (\<lambda>x n. True) 1 1 f_Id) 
    = FBlock (\<lambda>x n. True) 2 2 (\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) 
                           @ ((f_Id \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n))"
  proof -
    have inps_1: "inps (FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) f_Id) = 1"
      using s1 by (simp add: inps_P)
    have form: "((FBlock (\<lambda>x n. True) 1 1 f_Id) \<parallel>\<^sub>B (FBlock (\<lambda>x n. True) 1 1 f_Id)) = 
          (\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1, inouts\<^sub>0, inouts\<^sub>1) \<bullet> 
             (((takem (1+1) (1)) ;; (FBlock (\<lambda>x n. True) 1 1 f_Id))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
             ((dropm (1+1) (1)) ;; (FBlock (\<lambda>x n. True) 1 1 f_Id))\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
             (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a))) \<and>
             ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<guillemotright>))))"
      using s1 by (simp add: SimParallel_form)
    have 2: "(\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1, inouts\<^sub>0, inouts\<^sub>1) \<bullet> 
             (((takem (1+1) (1)) ;; (FBlock (\<lambda>x n. True) 1 1 f_Id))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
             ((dropm (1+1) (1)) ;; (FBlock (\<lambda>x n. True) 1 1 f_Id))\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
             (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a))) \<and>
             ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<guillemotright>)))) 
        = FBlock (\<lambda>x n. True) 2 2 (\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) 
                           @ ((f_Id \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n))"
      apply (simp add: FBlock_def f_Id_def takem_def dropm_def)
      apply (rel_auto)
      apply (simp add: f_Id_def)
      apply (rule_tac x = "ok\<^sub>v'" in exI)
      apply (rule_tac x = "ok\<^sub>v'" in exI)
      apply (rule_tac x = "inouts\<^sub>v'" in exI)
      apply (rule conjI)
      apply blast
      apply (rule_tac x = "\<lambda>na. []" in exI)
      apply blast
      apply (rule_tac x = "ok\<^sub>v'" in exI)
      apply (rule_tac x = "ok\<^sub>v'" in exI)
      apply (rule_tac x = "\<lambda>na. take (Suc 0) (inouts\<^sub>v na)" in exI)
      apply (rule conjI)
      apply (rule_tac x = "ok\<^sub>v'" in exI)
      apply (rule_tac x = "\<lambda>na. take (Suc 0) (inouts\<^sub>v na)" in exI)
      apply (metis (no_types, lifting) Nitpick.size_list_simp(2) f_Id_def less_numeral_extra(3) 
        list.sel(1) pos2 take_Suc take_eq_Nil take_tl)
      apply (rule_tac x = "\<lambda>na. drop (Suc 0) (inouts\<^sub>v na)" in exI)
      apply (rule conjI)
      apply (rule_tac x = "ok\<^sub>v'" in exI)
      apply (rule_tac x = "\<lambda>na. drop (Suc 0) (inouts\<^sub>v na)" in exI)
      apply (metis (no_types, lifting) Cons_nth_drop_Suc One_nat_def Suc_le_mono diff_Suc_1 
        drop_eq_Nil f_Id_def hd_drop_conv_nth le_numeral_extra(4) length_drop lessI numeral_2_eq_2)
      by (metis Cons_nth_drop_Suc Suc_1 Suc_eq_plus1 add.left_neutral append_take_drop_id drop_0 
        drop_eq_Nil lessI list.sel(1) order_refl take_Suc zero_less_Suc)
    show ?thesis
      using form 2
      by simp
  qed
  
lemma FBlock_parallel_comp:
  assumes s1: "SimBlock m1 n1 (FBlock (\<lambda>x n. True) m1 n1 f)"
  assumes s2: "SimBlock m2 n2 (FBlock (\<lambda>x n. True) m2 n2 g)"
  shows "(FBlock (\<lambda>x n. True) m1 n1 f) \<parallel>\<^sub>B (FBlock (\<lambda>x n. True) m2 n2 g) 
    = FBlock (\<lambda>x n. True) (m1+m2) (n1+n2) 
        (\<lambda>x n. (((f \<circ> (\<lambda>xx nn. take m1 (xx nn))) x n) @ ((g \<circ> (\<lambda>xx nn. drop m1 (xx nn)))) x n))"
  proof -
    have inps_1: "inps (FBlock (\<lambda>x n. True) m1 n1 f) = m1"
      using s1 by (simp add: inps_P)
    have inps_2: "inps (FBlock (\<lambda>x n. True) m2 n2 g) = m2"
      using s2 by (simp add: inps_P)
    have form: "((FBlock (\<lambda>x n. True) m1 n1 f) \<parallel>\<^sub>B (FBlock (\<lambda>x n. True) m2 n2 g)) = 
          (\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1, inouts\<^sub>0, inouts\<^sub>1) \<bullet> 
             (((takem (m1+m2) (m1)) ;; (FBlock (\<lambda>x n. True) m1 n1 f))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
             ((dropm (m1+m2) (m2)) ;; (FBlock (\<lambda>x n. True) m2 n2 g))\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
             (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a))) \<and>
             ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<guillemotright>))))"
      using s1 s2 by (simp add: SimParallel_form)
    have 2: "(\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1, inouts\<^sub>0, inouts\<^sub>1) \<bullet> 
             (((takem (m1+m2) (m1)) ;; (FBlock (\<lambda>x n. True) m1 n1 f))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
             ((dropm (m1+m2) (m2)) ;; (FBlock (\<lambda>x n. True) m2 n2 g))\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
             (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a))) \<and>
             ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<guillemotright>))))
        = FBlock (\<lambda>x n. True) (m1+m2) (n1+n2) 
          (\<lambda>x n. (((f \<circ> (\<lambda>xx nn. take m1 (xx nn))) x n) @ ((g \<circ> (\<lambda>xx nn. drop m1 (xx nn)))) x n))"
      apply (simp add: FBlock_def f_Id_def takem_def dropm_def)
      apply (rel_simp)
      apply (rule iffI)
      apply (clarify)
      apply (rule conjI, simp)
      apply (rule conjI, simp)
      proof -
        fix ok\<^sub>v inouts\<^sub>v inouts\<^sub>v' a aa ab ok\<^sub>v'' b inouts\<^sub>v''::"nat \<Rightarrow> real list" and ok\<^sub>v''' and 
          inouts\<^sub>v'''::"nat \<Rightarrow> real list"
        assume a1: "\<forall>x. (m1 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m2 \<and> inouts\<^sub>v'' x = []) \<and>
           (0 < m1 \<longrightarrow> length(inouts\<^sub>v x) = m1 + m2 \<and> take m1 (inouts\<^sub>v x) = inouts\<^sub>v'' x)"
        assume a2: " \<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m1 \<and> inouts\<^sub>v''' x = []) \<and>
           (0 < m2 \<longrightarrow> length(inouts\<^sub>v x) = m1 + m2 \<and> drop m1 (inouts\<^sub>v x) = inouts\<^sub>v''' x)"
        assume a3: "\<forall>x. length(inouts\<^sub>v'' x) = m1 \<and> length(ab x) = n1 \<and> f inouts\<^sub>v'' x = ab x"
        assume a4: "\<forall>x. length(inouts\<^sub>v''' x) = m2 \<and> length(b x) = n2 \<and> g inouts\<^sub>v''' x = b x"
        from a1 have 1: "\<forall>x. take m1 (inouts\<^sub>v x) = inouts\<^sub>v'' x"
          by fastforce
        then have 11: "inouts\<^sub>v'' = (\<lambda>x. take m1 (inouts\<^sub>v x))"
          using a1 by force
        from a3 have 2: "\<forall>x. f inouts\<^sub>v'' x = ab x"
          by blast
        from 11 and 2 have 3: "\<forall>x. f (\<lambda>x. take m1 (inouts\<^sub>v x)) x = ab x"
          by blast
        from a2 have g1: "\<forall>x. (drop m1 (inouts\<^sub>v x) = inouts\<^sub>v''' x)"
          by fastforce
        then have g11: "inouts\<^sub>v''' = (\<lambda>x. drop m1 (inouts\<^sub>v x))"
          by force
        from a4 have g2: "\<forall>x. g inouts\<^sub>v''' x = b x"
          by blast
        from g11 and g2 have g3: "\<forall>x. g (\<lambda>x. drop m1 (inouts\<^sub>v x)) x = b x"
          by blast
        show "\<forall>x. length(inouts\<^sub>v x) = m1 + m2 \<and> 
            f (\<lambda>nn. take m1 (inouts\<^sub>v nn)) x @ g (\<lambda>nn. drop m1 (inouts\<^sub>v nn)) x = ab x @ b x"
          apply (rule allI)
          apply (rule conjI)
          using a2 apply auto[1]
          by (simp add: "3" g3)
      next
        assume a1: "\<forall>x xa. length(x xa) = m1 \<longrightarrow> length(f x xa) = n1"
        assume a2: "\<forall>x xa. length(x xa) = m2 \<longrightarrow> length(g x xa) = n2"
        show "\<forall>x xa. length(x xa) = m1 + m2 \<longrightarrow> 
            length(f (\<lambda>nn. take m1 (x nn)) xa) + length(g (\<lambda>nn. drop m1 (x nn)) xa) = n1 + n2"
        using a1 a2 by simp
      next
        fix ok\<^sub>v inouts\<^sub>v ok\<^sub>v' inouts\<^sub>v'
        assume a1: "ok\<^sub>v \<longrightarrow>
         ok\<^sub>v' \<and>
         (\<forall>x. length(inouts\<^sub>v x) = m1 + m2 \<and>
              length(inouts\<^sub>v' x) = n1 + n2 \<and>
              f (\<lambda>nn. take m1 (inouts\<^sub>v nn)) x @ g (\<lambda>nn. drop m1 (inouts\<^sub>v nn)) x = inouts\<^sub>v' x) \<and>
         (\<forall>x xa. length(x xa) = m1 + m2 \<longrightarrow> 
              length(f (\<lambda>nn. take m1 (x nn)) xa) + length(g (\<lambda>nn. drop m1 (x nn)) xa) = n1 + n2)"
        from a1 show "\<exists>a aa ab.
          (\<exists>ok\<^sub>v' inouts\<^sub>v'.
              (ok\<^sub>v \<longrightarrow>
               ok\<^sub>v' \<and>
               (\<forall>x. (m1 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m2 \<and> inouts\<^sub>v' x = []) \<and>
                    (0 < m1 \<longrightarrow>
                     length(inouts\<^sub>v x) = m1 + m2 \<and> length(inouts\<^sub>v' x) = m1 \<and> take m1 (inouts\<^sub>v x) = inouts\<^sub>v' x))) \<and>
              (ok\<^sub>v' \<longrightarrow>
               a \<and> (\<forall>x. length(inouts\<^sub>v' x) = m1 \<and> length(ab x) = n1 \<and> f inouts\<^sub>v' x = ab x) \<and>
                    (\<forall>x xa. length(x xa) = m1 \<longrightarrow> length(f x xa) = n1))) \<and>
          (\<exists>b. (\<exists>ok\<^sub>v' inouts\<^sub>v'.
                   (ok\<^sub>v \<longrightarrow>
                    ok\<^sub>v' \<and>
                    (\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m1 \<and> inouts\<^sub>v' x = []) \<and>
                         (0 < m2 \<longrightarrow>
                          length(inouts\<^sub>v x) = m1 + m2 \<and>
                          length(inouts\<^sub>v' x) = m2 \<and> drop m1 (inouts\<^sub>v x) = inouts\<^sub>v' x))) \<and>
                   (ok\<^sub>v' \<longrightarrow>
                    aa \<and> (\<forall>x. length(inouts\<^sub>v' x) = m2 \<and> length(b x) = n2 \<and> g inouts\<^sub>v' x = b x) \<and>
                          (\<forall>x xa. length(x xa) = m2 \<longrightarrow> length(g x xa) = n2))) \<and>
               (\<forall>x. inouts\<^sub>v' x = ab x @ b x) \<and> ok\<^sub>v' = (a \<and> aa)) "
        apply (rel_auto)
        apply (rule_tac x = "ok\<^sub>v'" in exI)
        apply (rule_tac x = "ok\<^sub>v'" in exI)
        apply (rule_tac x = "inouts\<^sub>v'" in exI)
        apply (rule conjI)
        apply blast
        using take_0 apply blast
        apply (rule_tac x = "ok\<^sub>v'" in exI)
        apply (rule_tac x = "ok\<^sub>v'" in exI)
        apply (rule_tac x = "\<lambda>na. f (\<lambda>nx. take m1 (inouts\<^sub>v nx)) na" in exI)
        apply (rule conjI)
        apply (rule_tac x = "ok\<^sub>v'" in exI)
        apply (rule_tac x = "\<lambda>nx. take m1 (inouts\<^sub>v nx)" in exI)
        using SimBlock_FBlock_fn s1 apply auto[1]
        apply (rule_tac x = "\<lambda>na. g (\<lambda>nx. drop m1 (inouts\<^sub>v nx)) na" in exI)
        apply (rule conjI)
        apply (rule_tac x = "ok\<^sub>v'" in exI)
        apply (rule_tac x = "\<lambda>nx. drop m1 (inouts\<^sub>v nx)" in exI)
        using SimBlock_FBlock_fn s2 apply auto[1]
        by simp
      qed
    show ?thesis
      using 2 form by simp
  qed
   
lemma SimBlock_FBlock_parallel_comp [simblock_healthy]:
  assumes s1: "SimBlock m1 n1 (FBlock (\<lambda>x n. True) m1 n1 f)"
  assumes s2: "SimBlock m2 n2 (FBlock (\<lambda>x n. True) m2 n2 g)"
  shows "SimBlock (m1+m2) (n1+n2) ((FBlock (\<lambda>x n. True) m1 n1 f) \<parallel>\<^sub>B (FBlock (\<lambda>x n. True) m2 n2 g))"
  apply (simp add: "s1" "s2" FBlock_parallel_comp)
  apply (rule SimBlock_FBlock)
  proof -
    obtain inouts\<^sub>v::"nat \<Rightarrow> real list" where P: "\<forall>na. length(inouts\<^sub>v na) = m1 + m2"
      using list_len_avail by auto
    show "\<exists>inouts\<^sub>v inouts\<^sub>v'.
       \<forall>x. length(inouts\<^sub>v' x) = n1 + n2 \<and>
           length(inouts\<^sub>v x) = m1 + m2 \<and>
           f (\<lambda>nn. take m1 (inouts\<^sub>v nn)) x @ g (\<lambda>nn. drop m1 (inouts\<^sub>v nn)) x = inouts\<^sub>v' x"
      apply (rule_tac x = "inouts\<^sub>v" in exI)
      apply (rule_tac x = "\<lambda>na. (f (\<lambda>nn. take m1 (inouts\<^sub>v nn)) na @ g (\<lambda>nn. drop m1 (inouts\<^sub>v nn)) na)" in exI)
      using P SimBlock_FBlock_fn s1 s2 by auto
  next
    show "\<forall>x na. length(x na) = m1 + m2 \<longrightarrow> 
          length(f (\<lambda>nn. take m1 (x nn)) na @ g (\<lambda>nn. drop m1 (x nn)) na) = n1 + n2"
      using SimBlock_FBlock_fn s1 s2 by auto
  qed
(*
lemma FBlock_parallel_comp':
  assumes s1: "SimBlock m1 n1 (FBlock (\<lambda>x n. p1 x n \<and> length(x n) = m1) m1 n1 f)"
  assumes s2: "SimBlock m2 n2 (FBlock (\<lambda>x n. p2 x n \<and> length(x n) = m2) m2 n2 g)"
  shows "(FBlock (\<lambda>x n. p1 x n \<and> length(x n) = m1) m1 n1 f) \<parallel>\<^sub>B (FBlock (\<lambda>x n. p2 x n \<and> length(x n) = m2) m2 n2 g) 
    = FBlock (\<lambda>x n. (((\<lambda>x n. p1 x n) \<circ> (\<lambda>xx nn. take m1 (xx nn))) x n) \<and> 
            (((\<lambda>x n. p2 x n) \<circ> (\<lambda>xx nn. drop m1 (xx nn))) x n) \<and> length(x n) = m1 + m2) 
      (m1+m2) (n1+n2) 
        (\<lambda>x n. (((f \<circ> (\<lambda>xx nn. take m1 (xx nn))) x n) @ ((g \<circ> (\<lambda>xx nn. drop m1 (xx nn)))) x n))"
  proof -
    have inps_1: "inps (FBlock (\<lambda>x n. p1 x n \<and> length(x n) = m1) m1 n1 f) = m1"
      using s1 by (simp add: inps_P)
    have inps_2: "inps (FBlock (\<lambda>x n. p2 x n \<and> length(x n) = m2) m2 n2 g) = m2"
      using s2 by (simp add: inps_P)
    have form: "((FBlock (\<lambda>x n. p1 x n \<and> length(x n) = m1) m1 n1 f) \<parallel>\<^sub>B 
                 (FBlock (\<lambda>x n. p2 x n \<and> length(x n) = m2) m2 n2 g)) = 
          (\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1, inouts\<^sub>0, inouts\<^sub>1) \<bullet> 
             (((takem (m1+m2) (m1)) ;; (FBlock (\<lambda>x n. p1 x n \<and> length(x n) = m1) m1 n1 f))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
             ((dropm (m1+m2) (m2)) ;; (FBlock (\<lambda>x n. p2 x n \<and> length(x n) = m2) m2 n2 g))\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
             (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a))) \<and>
             ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<guillemotright>))))"
      using s1 s2 by (simp add: SimParallel_form)
    have 2: "(\<^bold>\<exists> (ok\<^sub>0, ok\<^sub>1, inouts\<^sub>0, inouts\<^sub>1) \<bullet> 
             (((takem (m1+m2) (m1)) ;; (FBlock (\<lambda>x n. p1 x n \<and> length(x n) = m1) m1 n1 f))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>inouts\<^sub>0\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and> 
             ((dropm (m1+m2) (m2)) ;; (FBlock (\<lambda>x n. p2 x n \<and> length(x n) = m2) m2 n2 g))\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>,\<guillemotleft>inouts\<^sub>1\<guillemotright>/$ok\<acute>,$\<^bold>v\<^sub>D:inouts\<acute>\<rbrakk> \<and>
             (\<^bold>\<forall> n::nat \<bullet> ($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>append\<guillemotright> (\<guillemotleft>inouts\<^sub>0 n\<guillemotright>)\<^sub>a (\<guillemotleft>inouts\<^sub>1 n\<guillemotright>)\<^sub>a))) \<and>
             ($ok\<acute> =\<^sub>u (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> \<guillemotleft>ok\<^sub>1\<guillemotright>))))
        = FBlock (\<lambda>x n. (((\<lambda>x n. p1 x n) \<circ> (\<lambda>xx nn. take m1 (xx nn))) x n) \<and> 
            (((\<lambda>x n. p2 x n) \<circ> (\<lambda>xx nn. drop m1 (xx nn))) x n)  \<and> length(x n) = m1 + m2) 
          (m1+m2) (n1+n2) 
          (\<lambda>x n. (((f \<circ> (\<lambda>xx nn. take m1 (xx nn))) x n) @ ((g \<circ> (\<lambda>xx nn. drop m1 (xx nn)))) x n))"
      apply (simp add: FBlock_def f_Id_def takem_def dropm_def)
      (* 
      apply (rule ref_eq)
      apply (simp add: ndesign_composition_wp wp_upred_def)
      apply (simp add: refBy_order)
      *)
      apply (rel_simp)
      apply (rule iffI)
      (* Subgoal 1: *)
      apply (clarify)
      apply (rule conjI, simp)
      apply (rename_tac ok\<^sub>v inouts\<^sub>v inouts\<^sub>v' ok\<^sub>v0 ok\<^sub>v1 inouts\<^sub>v0 ok\<^sub>v'' inouts\<^sub>v1 inouts\<^sub>vp1 ok\<^sub>v''' inouts\<^sub>vp2)
      (* Subgoal 2: *)
      defer
      apply (rename_tac ok\<^sub>v inouts\<^sub>v  ok\<^sub>v' inouts\<^sub>v' ok\<^sub>v0 ok\<^sub>v1 inouts\<^sub>v0 ok\<^sub>v'' inouts\<^sub>v1 inouts\<^sub>vp1 ok\<^sub>v''' inouts\<^sub>vp2)
      (* Subgoal 3: *)
      defer 
      apply (rule_tac x = "ok\<^sub>v'" in exI)
      apply (rule_tac x = "ok\<^sub>v'" in exI)
      apply (rule_tac x = "\<lambda>na. f (\<lambda>nn. take m1 (inouts\<^sub>v nn)) na" in exI)
      apply (rule conjI)
      apply (rule_tac x = "ok\<^sub>v \<and> (\<forall>x. p1 (\<lambda>nn. take m1 (inouts\<^sub>v nn)) x \<and>
                    min (length(inouts\<^sub>v x)) m1 = m1 \<and> 
                p2 (\<lambda>nn. drop m1 (inouts\<^sub>v nn)) x \<and> length(inouts\<^sub>v x) - m1 = m2)" in exI)
      apply (rule_tac x = "\<lambda>nn. take m1 (inouts\<^sub>v nn)" in exI)
      apply (rule conjI)
      apply (clarify)
      apply (rule conjI)
      apply (clarify)
      sledgehammer
      prefer 3
      proof -
        fix ok\<^sub>v inouts\<^sub>v::"nat \<Rightarrow> real list" and inouts\<^sub>v'::"nat \<Rightarrow> real list" and ok\<^sub>v0 ok\<^sub>v1 and 
            inouts\<^sub>v0::"nat \<Rightarrow> real list" and ok\<^sub>v'' inouts\<^sub>v1::"nat \<Rightarrow> real list" and 
            inouts\<^sub>vp1::"nat \<Rightarrow> real list" and ok\<^sub>v''' inouts\<^sub>vp2::"nat \<Rightarrow> real list"
        assume a1: "All (p1 inouts\<^sub>vp1) \<longrightarrow>
           ok\<^sub>v0 \<and>
           (\<forall>x. length(inouts\<^sub>vp1 x) = m1 \<and> length(inouts\<^sub>v0 x) = n1 \<and> f inouts\<^sub>vp1 x = inouts\<^sub>v0 x) \<and>
           (\<forall>x xa. length(f x xa) = n1)"
        assume a2: "All (p2 inouts\<^sub>vp2) \<longrightarrow>
           ok\<^sub>v1 \<and>
           (\<forall>x. length(inouts\<^sub>vp2 x) = m2 \<and> length(inouts\<^sub>v1 x) = n2 \<and> g inouts\<^sub>vp2 x = inouts\<^sub>v1 x) \<and>
           (\<forall>x xa. length(g x xa) = n2)"
        assume a3: "\<forall>x. p1 (\<lambda>nn. take m1 (inouts\<^sub>v nn)) x \<and> p2 (\<lambda>nn. drop m1 (inouts\<^sub>v nn)) x"
        assume a4: "\<forall>x. (m1 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m2 \<and> inouts\<^sub>vp1 x = []) \<and>
           (0 < m1 \<longrightarrow>
            length(inouts\<^sub>v x) = m1 + m2 \<and> length(inouts\<^sub>vp1 x) = m1 \<and> take m1 (inouts\<^sub>v x) = inouts\<^sub>vp1 x)"
        assume a5: "\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m1 \<and> inouts\<^sub>vp2 x = []) \<and>
           (0 < m2 \<longrightarrow>
            length(inouts\<^sub>v x) = m1 + m2 \<and> length(inouts\<^sub>vp2 x) = m2 \<and> drop m1 (inouts\<^sub>v x) = inouts\<^sub>vp2 x)"
        from a4 have a4': "\<forall>x. take m1 (inouts\<^sub>v x) = inouts\<^sub>vp1 x"
          by auto
        from a4' have a4'': "(\<lambda>x. take m1 (inouts\<^sub>v x)) = inouts\<^sub>vp1"
          by blast
        from a5 have a5': "\<forall>x. drop m1 (inouts\<^sub>v x) = inouts\<^sub>vp2 x"
          by auto
        from a5' have a5'': "(\<lambda>x. drop m1 (inouts\<^sub>v x)) = inouts\<^sub>vp2"
          by auto
        from a3 have "\<forall>x. p1 (\<lambda>nn. take m1 (inouts\<^sub>v nn)) x"
          by simp
        then have a1': "\<forall>x. p1 inouts\<^sub>vp1 x"
          using a4'' by blast
        from a3 have "\<forall>x. p2 (\<lambda>nn. drop m1 (inouts\<^sub>v nn)) x"
          by simp
        then have a2': "\<forall>x. p2 inouts\<^sub>vp2 x"
          using a5'' by blast
        from a1' a2' a1 a2 show "ok\<^sub>v0 \<and> ok\<^sub>v1"
          by auto
      next
        fix ok\<^sub>v inouts\<^sub>v::"nat \<Rightarrow> real list" and ok\<^sub>v' inouts\<^sub>v'::"nat \<Rightarrow> real list" and ok\<^sub>v0 ok\<^sub>v1 and 
            inouts\<^sub>v0::"nat \<Rightarrow> real list" and ok\<^sub>v''::bool and inouts\<^sub>v1::"nat \<Rightarrow> real list" and 
            inouts\<^sub>vp1::"nat \<Rightarrow> real list" and ok\<^sub>v'''::bool and inouts\<^sub>vp2::"nat \<Rightarrow> real list"
        assume a1: "ok\<^sub>v'' \<and> All (p1 inouts\<^sub>vp1) \<longrightarrow>
           ok\<^sub>v0 \<and>
           (\<forall>x. length(inouts\<^sub>vp1 x) = m1 \<and> length(inouts\<^sub>v0 x) = n1 \<and> f inouts\<^sub>vp1 x = inouts\<^sub>v0 x) \<and>
           (\<forall>x xa. length(f x xa) = n1)"
        assume a2: "ok\<^sub>v''' \<and> All (p2 inouts\<^sub>vp2) \<longrightarrow>
           ok\<^sub>v1 \<and>
           (\<forall>x. length(inouts\<^sub>vp2 x) = m2 \<and> length(inouts\<^sub>v1 x) = n2 \<and> g inouts\<^sub>vp2 x = inouts\<^sub>v1 x) \<and>
           (\<forall>x xa. length(g x xa) = n2)"
        assume a3: "\<forall>x. p1 (\<lambda>nn. take m1 (inouts\<^sub>v nn)) x \<and> p2 (\<lambda>nn. drop m1 (inouts\<^sub>v nn)) x"
        assume a4: "\<forall>x. (m1 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m2 \<and> inouts\<^sub>vp1 x = []) \<and>
           (0 < m1 \<longrightarrow>
            length(inouts\<^sub>v x) = m1 + m2 \<and> length(inouts\<^sub>vp1 x) = m1 \<and> take m1 (inouts\<^sub>v x) = inouts\<^sub>vp1 x)"
        assume a5: "\<forall>x. (m2 = 0 \<longrightarrow> length(inouts\<^sub>v x) = m1 \<and> inouts\<^sub>vp2 x = []) \<and>
           (0 < m2 \<longrightarrow>
            length(inouts\<^sub>v x) = m1 + m2 \<and> length(inouts\<^sub>vp2 x) = m2 \<and> drop m1 (inouts\<^sub>v x) = inouts\<^sub>vp2 x)"  
        assume a6: "\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v0 x @ inouts\<^sub>v1 x"      
        assume a7: "ok\<^sub>v''" and a8: "ok\<^sub>v'''"
        from a4 have a4': "\<forall>x. take m1 (inouts\<^sub>v x) = inouts\<^sub>vp1 x"
          by auto
        from a4' have a4'': "(\<lambda>x. take m1 (inouts\<^sub>v x)) = inouts\<^sub>vp1"
          by blast
        from a5 have a5': "\<forall>x. drop m1 (inouts\<^sub>v x) = inouts\<^sub>vp2 x"
          by auto
        from a5' have a5'': "(\<lambda>x. drop m1 (inouts\<^sub>v x)) = inouts\<^sub>vp2"
          by auto
        from a3 have "\<forall>x. p1 (\<lambda>nn. take m1 (inouts\<^sub>v nn)) x"
          by simp
        then have a1': "\<forall>x. p1 inouts\<^sub>vp1 x"
          using a4'' by blast
        from a3 have "\<forall>x. p2 (\<lambda>nn. drop m1 (inouts\<^sub>v nn)) x"
          by simp
        then have a2': "\<forall>x. p2 inouts\<^sub>vp2 x"
          using a5'' by blast
        from a1' a1 a7 have a1'': "\<forall>x. f inouts\<^sub>vp1 x = inouts\<^sub>v0 x"
          by blast
        from a2' a2 a8 have a2'': "\<forall>x. g inouts\<^sub>vp2 x = inouts\<^sub>v1 x"
          by blast
        show "(\<forall>x. length(inouts\<^sub>v x) = m1 + m2 \<and> length(inouts\<^sub>v' x) = n1 + n2 \<and>
            f (\<lambda>nn. take m1 (inouts\<^sub>v nn)) x @ g (\<lambda>nn. drop m1 (inouts\<^sub>v nn)) x = inouts\<^sub>v' x) \<and>
            (\<forall>x xa. length(f (\<lambda>nn. take m1 (x nn)) xa) + length(g (\<lambda>nn. drop m1 (x nn)) xa) = n1 + n2)"
          apply (simp add: a4'' a5'')
          apply (rule conjI)
          using a1 a1' a2 a2' a5 a6 a7 a8 apply auto[1]
          using SimBlock_FBlock_fn' s1 s2 by auto
      next
  qed
*)

subsubsection {* Feedback *}
(*
(* (Sum2 ;; UD ;; Split) fd (1,1) *)
lemma sol_f_integrator: 
  "(FBlock (\<lambda>x n. True) 2 2 (\<lambda>x n. [if n = 0 then x0 else (x (n-1)!0) + (x (n-1)!1),
      if n = 0 then x0 else (x (n-1)!0) + (x (n-1)!1)])) f\<^sub>D (1,1) = 
  FBlock (\<lambda>x n. True) 1 1 
    (\<lambda>x n. [(SOME xx. (xx n = (if n = 0 then x0 else (x (n-1)!0) + (xx (n-1))))) n])"
  proof -
    have 1: "SimBlock 2 2 (FBlock (\<lambda>x n. True) 2 2 (\<lambda>x n. [if n = 0 then x0 else (x (n-1)!0) + (x (n-1)!1),
      if n = 0 then x0 else (x (n-1)!0) + (x (n-1)!1)]))"
    sorry
    from 1 have inps_1: "inps (FBlock (\<lambda>x n. True) 2 2 (\<lambda>x n. [if n = 0 then x0 else (x (n-1)!0) + (x (n-1)!1),
      if n = 0 then x0 else (x (n-1)!0) + (x (n-1)!1)])) = 2"
      using inps_P by blast 
    from 1 have outps_1: "outps (FBlock (\<lambda>x n. True) 2 2 (\<lambda>x n. [if n = 0 then x0 else (x (n-1)!0) + (x (n-1)!1),
      if n = 0 then x0 else (x (n-1)!0) + (x (n-1)!1)])) = 2"
      using outps_P by blast 
    show ?thesis
      apply (simp add: f_sim_blocks inps_1 outps_1)
      apply (simp add: FBlock_def)
      apply (simp add: f_PreFD_def f_PostFD_def)
      apply (rel_auto)
      apply blast
      apply (rule_tac x = "\<lambda>x. (SOME xx. (x = 0 \<longrightarrow> xx 0 = x0) \<and> 
              (0 < x \<longrightarrow> xx x = inouts\<^sub>v (x - Suc 0)!(0) + xx (x - Suc 0))) x" in exI)
      apply (rule_tac x = "True" in exI)
      apply (rule_tac x = "\<lambda>x. [hd(inouts\<^sub>v x), (SOME xx. (x = 0 \<longrightarrow> xx 0 = x0) \<and> 
              (0 < x \<longrightarrow> xx x = inouts\<^sub>v (x - Suc 0)!(0) + xx (x - Suc 0))) x]" in exI)
      apply (simp)
      apply (rule conjI)
      apply (clarify)
*)

paragraph {* feedback *}

lemma feedback_mono:
  fixes m1 :: nat and n1 :: nat and i1 :: nat and o1 :: nat
  assumes s1: "SimBlock m1 n1 P1"
  assumes s2: "SimBlock m1 n1 P2" 
  assumes s3: "P1 \<sqsubseteq> P2"
  assumes s4: "i1 < m1"
  assumes s5: "o1 < n1"
  shows "(P1 f\<^sub>D (i1,o1)) \<sqsubseteq> (P2 f\<^sub>D (i1,o1))"
  apply (simp add: f_sim_blocks)
  using s1 s2 apply (simp add: inps_P outps_P)
  apply (rel_simp)
  apply (auto)
  apply (metis s3 upred_ref_iff)
  apply (rule_tac x = "x" in exI)
  apply (rule_tac x = "ok\<^sub>v''" in exI)
  apply (rule_tac x = "inouts\<^sub>v''" in exI)
  apply (rule_tac x = "ok\<^sub>v'''" in exI)
  apply (rule_tac x = "inouts\<^sub>v'''" in exI)
  apply (metis s3 upred_ref_iff)
  apply (rule_tac x = "x" in exI)
  apply (rule_tac x = "True" in exI)
  apply (rule_tac x = "inouts\<^sub>v''" in exI)
  apply (rule conjI)
  apply blast
  apply (rule_tac x = "False" in exI)
  apply (rule_tac x = "inouts\<^sub>v'''" in exI)
  apply (meson s3 upred_ref_iff)
  apply (rule_tac x = "x" in exI)
  apply (rule_tac x = "True" in exI)
  apply (rule_tac x = "inouts\<^sub>v''" in exI)
  apply (rule conjI)
  apply blast
  apply (rule_tac x = "ok\<^sub>v'''" in exI)
  apply (rule_tac x = "inouts\<^sub>v'''" in exI)
  by (metis s3 upred_ref_iff)

(*
lemma feedback_assoc:
  fixes m1 :: nat and n1 :: nat and i1 :: nat and o1 :: nat
  assumes s1: "SimBlock m1 n1 P1"
  assumes s2: "i1 < m1"
  assumes s3: "i2 < m1"
  assumes s4: "o1 < n1"
  assumes s5: "o2 < n1"
  shows "((P1 f\<^sub>D (i1,o1)) f\<^sub>D (i2,o2))  \<sqsubseteq> ((P1 f\<^sub>D (i2,o2)) f\<^sub>D (i1,o1))"
  apply (simp add: sim_blocks)
sorry
*)

(* Invalid feedback pair since Id only has one input and one output *)
(*
lemma "Id f\<^sub>D (0,1) = \<top>\<^sub>D"
  apply (simp add: SimBlock_Id inps_P outps_P)
  apply (simp add: inps_id outps_id)
  apply (simp add: Id_def FBlock_def)
  apply (simp add: PreFD_def PostFD_def Id_def)
  apply (rel_auto)
done
*)

lemma sol_f_id: "Solvable 0 0 1 1 f_Id"
  by (simp add: Solvable_def f_Id_def f_PreFD_def)

lemma sol_f_ud: "Solvable 0 0 1 1 (f_UnitDelay x0)"
  apply (simp add: Solvable_def f_UnitDelay_def f_PreFD_def)
  by (auto)

-- {* The function which output is equal to its input plus 1 is not solvable *}
lemma "\<not> Solvable 0 0 1 1 (\<lambda>x n. [hd(x n) + 1])"
  apply (simp add: Solvable_def f_PreFD_def)
  by (auto)

lemma sol_f_id_ud: "Solvable 0 0 1 1 ((f_UnitDelay x0) \<circ> (f_Id))"
  apply (simp add: Solvable_def f_UnitDelay_def f_Id_def f_PreFD_def)
  by (auto)

(* (Sum2 ;; UD ;; Split) fd (1,1) *)
lemma sol_f_integrator: 
  "Solvable 1 1 2 2 (\<lambda>x n. [if n = 0 then x0 else (x (n-1)!0) + (x (n-1)!1),
      if n = 0 then x0 else (x (n-1)!0) + (x (n-1)!1)])"
  apply (simp add: Solvable_def f_PreFD_def)
  apply (clarify)
  apply (rule_tac x = "\<lambda>na. (if na = 0 then x0 else (x0+sum_hd_signal inouts\<^sub>0 (na-1)))" in exI)
  apply (simp, clarify)
  apply (rule conjI)
  apply (clarify)
  apply (metis Nil_is_append_conv One_nat_def add.commute hd_append2 hd_conv_nth list.size(3) 
      nth_append_length zero_neq_one)
  apply (clarify)
  proof -
    fix inouts\<^sub>0::"nat \<Rightarrow> real list" and n::nat
    assume a1: "\<forall>x. length(inouts\<^sub>0 x) = Suc 0"
    assume a2: "\<not> n \<le> Suc 0"
    have 1: "(inouts\<^sub>0 (n - Suc 0) @ [x0 + sum_hd_signal inouts\<^sub>0 (n - Suc (Suc 0))])!(0)
      = hd(inouts\<^sub>0 (n - Suc 0))"
      using a1 a2
      by (metis One_nat_def hd_conv_nth le_numeral_extra(4) less_numeral_extra(1) list.size(3) 
          not_one_le_zero nth_append)
    have 2: "(inouts\<^sub>0 (n - Suc 0) @ [x0 + sum_hd_signal inouts\<^sub>0 (n - Suc (Suc 0))])!(Suc 0)
      = x0 + sum_hd_signal inouts\<^sub>0 (n - Suc (Suc 0))"
      using a1 a2
      by (metis nth_append_length)
    have 3: "(n - (Suc 0)) = Suc (n - (Suc (Suc 0)))"
      using a2 by linarith
    show "x0 + sum_hd_signal inouts\<^sub>0 (n - Suc 0) =
       (inouts\<^sub>0 (n - Suc 0) @ [x0 + sum_hd_signal inouts\<^sub>0 (n - Suc (Suc 0))])!(0) +
       (inouts\<^sub>0 (n - Suc 0) @ [x0 + sum_hd_signal inouts\<^sub>0 (n - Suc (Suc 0))])!(Suc 0)"
      apply (simp add: "1" "2")
      using a1 a2 3
      by simp
  qed

lemma Solvable_unique_is_solvable:
  assumes "Solvable_unique i1 o1 m n (f)"
  shows "Solvable i1 o1 m n (f)"
  using assms apply (simp add: Solvable_unique_def Solvable_def)
  apply (clarify)
  by blast

text {* @{text "unique_solution_integrator"}: the integrator diagram has a unique solution. *}
lemma unique_solution_integrator:
  fixes inouts\<^sub>0::"nat \<Rightarrow> real list"
  assumes s1: "\<forall>n. length(inouts\<^sub>0 n) = 1"
  shows "\<exists>!xx. (\<forall>n. (n = 0 \<longrightarrow> xx 0 = x0) \<and>
              (0 < n \<longrightarrow> xx n = hd((inouts\<^sub>0 (n - Suc 0))) + xx (n - Suc 0)))"
    apply (rule ex_ex1I)
    apply (rule_tac x = "\<lambda>na. (if na = 0 then x0 else (x0+(\<Sum>i \<in> {0..(na-1)}. hd((inouts\<^sub>0 i)))))" in exI)
    apply (simp)
    apply (rule allI)
    proof -
      fix n::nat
      show " \<not> n \<le> Suc 0 \<longrightarrow>
         (\<Sum>i = 0..n - Suc 0. hd (inouts\<^sub>0 i)) =
         hd (inouts\<^sub>0 (n - Suc 0)) + (\<Sum>i = 0..n - Suc (Suc 0). hd (inouts\<^sub>0 i))"
        proof (induct "n")
          case 0
          thus ?case by auto
        next
          case (Suc n) note IH = this
          { assume "Suc n = 1"
             hence ?case by auto    
          }
          also {
            assume "Suc n > 1"
            {
              assume "Suc n = 2"
              hence ?case by auto 
            }
            also {
              assume "Suc n > 2"
              have ?case 
                by (smt One_nat_def Suc_diff_Suc \<open>1 < Suc n\<close> sum.atLeast0_atMost_Suc)
            }
          }
          
          ultimately show ?case
            by (smt One_nat_def Suc_1 Suc_lessI cancel_comm_monoid_add_class.diff_cancel 
                diff_Suc_1 not_less sum.atLeast0_atMost_Suc)
        qed
    next
      fix xx:: "nat \<Rightarrow> real" and y:: "nat \<Rightarrow> real"
      assume a1: "\<forall>n. (n = 0 \<longrightarrow> xx 0 = x0) \<and> (0 < n \<longrightarrow> xx n = hd (inouts\<^sub>0 (n - Suc 0)) + xx (n - Suc 0))"
      assume a2: "\<forall>n. (n = 0 \<longrightarrow> y 0 = x0) \<and> (0 < n \<longrightarrow> y n = hd (inouts\<^sub>0 (n - Suc 0)) + y (n - Suc 0))"
      have 1: "\<forall>n. xx n = y n"
        apply (rule allI)
        proof -
          fix n::nat
          show "xx n = y n"
            proof (induct n)
              case 0
              then show ?case 
                using a1 a2 by simp
            next
              case (Suc n) note IH = this
              then show ?case
                using a1 a2 by simp
            qed
        qed
      show "xx = y"
        using 1 fun_eq by (blast)
    qed

lemma FBlock_feedback:
  assumes s1: "SimBlock m n (FBlock (\<lambda>x n. True) m n f)"
  assumes s2: "Solvable_unique i1 o1 m n (f)"
  shows "(FBlock (\<lambda>x n. True) m n f) f\<^sub>D (i1, o1) 
       = (FBlock (\<lambda>x n. True) (m-1) (n-1)
            (\<lambda>x na. ((f_PostFD o1) o f o (f_PreFD (Solution i1 o1 m n f x) i1)) x na))"
  proof -
    have inps_1: "inps (FBlock (\<lambda>x n. True) m n f) = m"
      using s1 by (simp add: inps_P)
    have outps_1: "outps (FBlock (\<lambda>x n. True) m n f) = n"
      using s1 by (simp add: outps_P)
    have i1_lt_m: "i1 < m" 
      using s2 by (simp add: Solvable_unique_def)
    have o1_lt_n: "o1 < n" 
      using s2 by (simp add: Solvable_unique_def)
    have 1: "(FBlock (\<lambda>x n. True) m n f) f\<^sub>D (i1, o1) = (true \<turnstile>\<^sub>n (\<^bold>\<exists> x \<bullet> 
            (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m - Suc 0\<guillemotright> \<and>
                    #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m\<guillemotright> \<and> $inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>f_PreFD x i1\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>n\<guillemotright>)\<^sub>a) ;;
            ((\<^bold>\<forall> na \<bullet> #\<^sub>u($inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m\<guillemotright> \<and>
                      #\<^sub>u($inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> \<guillemotleft>f\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>na\<guillemotright>)\<^sub>a =\<^sub>u $inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a) \<and>
             (\<^bold>\<forall> x \<bullet> \<^bold>\<forall> na \<bullet> #\<^sub>u(\<guillemotleft>x na\<guillemotright>) =\<^sub>u \<guillemotleft>m\<guillemotright> \<Rightarrow> #\<^sub>u(\<guillemotleft>f x na\<guillemotright>) =\<^sub>u \<guillemotleft>n\<guillemotright>)) ;;
            (\<^bold>\<forall> na \<bullet> #\<^sub>u($inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and>
                     #\<^sub>u($inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n - Suc 0\<guillemotright> \<and>
                     $inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>f_PostFD o1\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>na\<guillemotright>)\<^sub>a \<and>
                     \<guillemotleft>uapply\<guillemotright>($inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a)\<^sub>a(\<guillemotleft>o1\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>x na\<guillemotright>)))"
      apply (simp add: inps_1 outps_1)
      apply (simp add: PreFD_def PostFD_def FBlock_def Solution_def)
      apply (simp add: ndesign_composition_wp wp_upred_def)
      by (rel_simp)
    have 2: "(true \<turnstile>\<^sub>n (\<^bold>\<exists> x \<bullet> 
            (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m - Suc 0\<guillemotright> \<and>
                    #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m\<guillemotright> \<and> $inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>f_PreFD x i1\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>n\<guillemotright>)\<^sub>a) ;;
            ((\<^bold>\<forall> na \<bullet> #\<^sub>u($inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m\<guillemotright> \<and>
                      #\<^sub>u($inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> \<guillemotleft>f\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>na\<guillemotright>)\<^sub>a =\<^sub>u $inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a) \<and>
             (\<^bold>\<forall> x \<bullet> \<^bold>\<forall> na \<bullet> #\<^sub>u(\<guillemotleft>x na\<guillemotright>) =\<^sub>u \<guillemotleft>m\<guillemotright> \<Rightarrow> #\<^sub>u(\<guillemotleft>f x na\<guillemotright>) =\<^sub>u \<guillemotleft>n\<guillemotright>)) ;;
            (\<^bold>\<forall> na \<bullet> #\<^sub>u($inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and>
                     #\<^sub>u($inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n - Suc 0\<guillemotright> \<and>
                     $inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>f_PostFD o1\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>na\<guillemotright>)\<^sub>a \<and>
                     \<guillemotleft>uapply\<guillemotright>($inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a)\<^sub>a(\<guillemotleft>o1\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>x na\<guillemotright>)))
      = (FBlock (\<lambda>x n. True) (m-1) (n-1)
            (\<lambda>x na. ((f_PostFD o1) o f o (f_PreFD (Solution i1 o1 m n f x) i1)) x na))"
      apply (simp add: FBlock_def Solution_def)
      apply (rule ref_eq)
      apply (rule ndesign_refine_intro, simp+)
      apply (rel_simp)
      apply (rule_tac x = "(SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1))" in exI)
      apply (rule_tac x = "\<lambda>na. f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) 
                                        i1 inouts\<^sub>v na" in exI, simp)
      apply (rule conjI)
      apply (simp add: f_PreFD_def)
      using i1_lt_m apply linarith
      apply (rule_tac x = "\<lambda>na. (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1))
                                             i1 inouts\<^sub>v) na)" in exI, simp)
      apply (rule conjI)
      apply (simp add: f_PreFD_def)
      apply (rule conjI)
      using i1_lt_m apply linarith
      (* using SimBlock_FBlock_fn s1 sledgehammer*)
      defer
      apply (rule conjI)
      using SimBlock_FBlock_fn s1 apply blast
      apply (rule allI, rule conjI)
      (* using SimBlock_FBlock_fn s1 apply blast *)
      defer
      defer
      apply (rule ndesign_refine_intro, simp+)
      apply (rel_simp)
      apply (rule conjI)
      defer
      apply (simp add: f_PreFD_def f_PostFD_def) 
      using o1_lt_n apply linarith
      prefer 3
      proof -
        fix inouts\<^sub>v::"nat \<Rightarrow> real list" and inouts\<^sub>v'::"nat \<Rightarrow> real list" and x::nat
        assume a1: "\<forall>x. length(inouts\<^sub>v x) = m - Suc 0 \<and>
           length(inouts\<^sub>v' x) = n - Suc 0 \<and>
           f_PostFD o1 (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v)) x = inouts\<^sub>v' x"
        let ?P= "\<lambda>xx.  \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)"
        have 1: "(?P (SOME xx. ?P xx))"
          apply (rule someI_ex[of "?P"])
          using s2 apply (simp add: Solvable_unique_def)
          using a1 by blast
        show "f (f_PreFD (SOME xx. ?P xx) i1 inouts\<^sub>v) x!(o1) = (SOME xx. ?P xx) x"
          by (simp add: "1")
      next 
        fix inouts\<^sub>v inouts\<^sub>v'
        assume a1: "\<forall>x. length(inouts\<^sub>v x) = m - Suc 0 \<and>
           length(inouts\<^sub>v' x) = n - Suc 0 \<and>
           f_PostFD o1 (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v)) x =
           inouts\<^sub>v' x"
        assume a2: "\<forall>x xa. length(x xa) = m - Suc 0 \<longrightarrow>
              length(f_PostFD o1 (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 x) n!(o1)) i1 x)) xa) =
              n - Suc 0"
        from a1 have a1': "\<forall>x. length(inouts\<^sub>v x) = m - Suc 0"
          by (simp)
        have "\<forall>na. length((f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v) na) = m"
          using a1' f_PreFD_def apply (simp)
          using i1_lt_m by linarith
        then show "\<forall>x. length(f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v) x) = n"
          using SimBlock_FBlock_fn s1 by blast
      next
        fix inouts\<^sub>v inouts\<^sub>v' x
        assume a1: "\<forall>x. length(inouts\<^sub>v x) = m - Suc 0 \<and>
           length(inouts\<^sub>v' x) = n - Suc 0 \<and>
           f_PostFD o1 (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v)) x =
           inouts\<^sub>v' x"
        assume a2: "\<forall>x xa. length(x xa) = m - Suc 0 \<longrightarrow>
              length(f_PostFD o1 (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 x) n!(o1)) i1 x)) xa) =
              n - Suc 0"
        from a1 have a1': "\<forall>x. length(inouts\<^sub>v x) = m - Suc 0"
          by (simp)
        have "\<forall>na. length((f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v) na) = m"
          using a1' f_PreFD_def apply (simp)
          using i1_lt_m by linarith
        then show "length(f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v) x) = n"
          using SimBlock_FBlock_fn s1 by blast
      next
        fix inouts\<^sub>v::"nat \<Rightarrow> real list" and inouts\<^sub>v'::"nat \<Rightarrow> real list" and x::"nat \<Rightarrow> real" and 
            inouts\<^sub>v''::"nat \<Rightarrow> real list" and inouts\<^sub>v'''::"nat \<Rightarrow> real list"
        assume a1: "\<forall>xa. length(inouts\<^sub>v xa) = m - Suc 0 \<and> inouts\<^sub>v'' xa = f_PreFD x i1 inouts\<^sub>v xa" 
        assume a2: "\<forall>xa. length(f_PreFD x i1 inouts\<^sub>v xa) = m \<and> f inouts\<^sub>v'' xa = inouts\<^sub>v''' xa" 
        assume a3: "\<forall>xa. length(inouts\<^sub>v''' xa) = n \<and> length(inouts\<^sub>v' xa) = n - Suc 0 \<and> 
                        inouts\<^sub>v' xa = f_PostFD o1 inouts\<^sub>v''' xa \<and> inouts\<^sub>v''' xa!(o1) = x xa"
        have unique_sol: "
          (\<exists>! (xx::nat \<Rightarrow> real). 
            (\<forall>n. (xx n = (f (\<lambda>n1. f_PreFD xx i1 inouts\<^sub>v n1) n)!o1)))"
          using s2 a1 by (simp add: Solvable_unique_def)
        from a1 a2 have "\<forall>xa. inouts\<^sub>v''' xa = f inouts\<^sub>v'' xa"
          by simp
        then have "\<forall>xa. inouts\<^sub>v''' xa = f (f_PreFD x i1 inouts\<^sub>v) xa"
          using a1 by presburger
        then have 0: "inouts\<^sub>v''' = f (f_PreFD x i1 inouts\<^sub>v)" 
          by (rule fun_eq)
        have 1: "(SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) = x" 
          apply (rule some_equality)
          using "0" a3 unique_sol by auto
        then have 2: "\<forall>n. f_PostFD o1 (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v)) n 
         = f_PostFD o1 (f (f_PreFD x i1 inouts\<^sub>v)) n"
          by blast
        then have 3: "\<forall>n. f_PostFD o1 (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v)) n 
         = f_PostFD o1 inouts\<^sub>v''' n"
          using 0 by blast
        show "\<forall>x. length(f_PostFD o1 inouts\<^sub>v''' x) = n - Suc 0 \<and>
           f_PostFD o1 (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v)) x 
         = f_PostFD o1 inouts\<^sub>v''' x"
          apply (rule allI, rule conjI)
          apply (simp add: f_PostFD_def)
          using a3 o1_lt_n apply auto[1]
          using 3 by blast
      qed
    show ?thesis
      using 1 by (simp add: "2")
  qed

lemma unique_solution:
  assumes s1: "Solvable_unique i1 o1 m n (f)"
  assumes s2: "is_Solution i1 o1 m n (f) (xx)"
  assumes s3: "\<forall>n. length(ins n) = m-1"
  shows "xx ins = (Solution i1 o1 m n f ins)"
  using s1 s2 apply (simp add: Solution_def Solvable_unique_def is_Solution_def)
  apply (clarify)
  proof -
    assume a1: "\<forall>inouts\<^sub>0. (\<forall>x. length(inouts\<^sub>0 x) = m - Suc 0) \<longrightarrow> 
                (\<forall>n.  xx inouts\<^sub>0 n = f (f_PreFD (xx inouts\<^sub>0) i1 inouts\<^sub>0) n!(o1))"
    assume a2: "\<forall>inouts\<^sub>0. (\<forall>x. length(inouts\<^sub>0 x) = m - Suc 0) \<longrightarrow> 
                (\<exists>!xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>0) n!(o1))"
    have "(SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 ins) n!(o1)) = xx ins"
      apply (rule some_equality)
      using a1 s3 apply simp
      using a2 apply (simp add: Ex1_def)
      proof -
        fix xxa
        assume a3: "\<forall>n. xxa n = f (f_PreFD xxa i1 ins) n!(o1)"
        assume a4: " \<forall>inouts\<^sub>0.
              (\<forall>x. length(inouts\<^sub>0 x) = m - Suc 0) \<longrightarrow>
              (\<exists>x. (\<forall>n. x n = f (f_PreFD x i1 inouts\<^sub>0) n!(o1)) \<and>
                   (\<forall>y. (\<forall>n. y n = f (f_PreFD y i1 inouts\<^sub>0) n!(o1)) \<longrightarrow> y = x))"
        from a4 s3 have 1: "(\<exists>x. (\<forall>n. x n = f (f_PreFD x i1 ins) n!(o1)) \<and>
                   (\<forall>y. (\<forall>n. y n = f (f_PreFD y i1 ins) n!(o1)) \<longrightarrow> y = x))"
          by simp
        from s2 have 2: "\<forall>n. (xx ins) n = f (f_PreFD (xx ins) i1 ins) n!(o1)"
          using a1 s3 by simp
        show "xxa = xx ins"
          using a3 a4 s3 1 2 by blast
      qed
    then show "xx ins = (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 ins) n!(o1))"
      by simp
  qed

lemma FBlock_feedback':
  assumes s1: "SimBlock m n (FBlock (\<lambda>x n. True) m n f)"
  assumes s2: "Solvable_unique i1 o1 m n (f)"
  assumes s3: "is_Solution i1 o1 m n (f) (xx)"
  shows "(FBlock (\<lambda>x n. True) m n f) f\<^sub>D (i1, o1) 
       = (FBlock (\<lambda>x n. True) (m-1) (n-1)
            (\<lambda>x na. ((f_PostFD o1) o f o (f_PreFD (xx x) i1)) x na))"
    using s1 s2 FBlock_feedback apply (simp)
    proof -
      have i1_lt_m: "i1 < m" 
        using s2 by (simp add: Solvable_unique_def)
      have o1_lt_n: "o1 < n" 
        using s2 by (simp add: Solvable_unique_def)
      show "FBlock (\<lambda>x n. True) (m - Suc 0) (n - Suc 0) 
              (\<lambda>x. f_PostFD o1 (f (f_PreFD (Solution i1 o1 m n f x) i1 x))) =
        FBlock (\<lambda>x n. True) (m - Suc 0) (n - Suc 0) (\<lambda>x. f_PostFD o1 (f (f_PreFD (xx x) i1 x)))"
      apply (simp (no_asm) add: FBlock_def)
      apply (rel_simp)
      apply (rule iffI, clarify)
      defer
      apply (clarify)
      defer
      proof -
        fix ok\<^sub>v inouts\<^sub>v ok\<^sub>v' inouts\<^sub>v'
        assume a1: "\<forall>x. length(inouts\<^sub>v x) = m - Suc 0 \<and>
           length(inouts\<^sub>v' x) = n - Suc 0 \<and>
           f_PostFD o1 (f (f_PreFD (Solution i1 o1 m n f inouts\<^sub>v) i1 inouts\<^sub>v)) x = inouts\<^sub>v' x"
        assume a2: "\<forall>x xa. length(x xa) = m - Suc 0 \<longrightarrow> 
           length(f_PostFD o1 (f (f_PreFD (Solution i1 o1 m n f x) i1 x)) xa) = n - Suc 0"
        have 1: "\<forall>x. length(inouts\<^sub>v x) = m - Suc 0"
          using a1 by simp
        have 2: "xx inouts\<^sub>v = (Solution i1 o1 m n f inouts\<^sub>v)"
          apply (rule unique_solution)
          using s2 apply (simp)
          using s3 apply (simp)
          using 1 by (simp)
        show "(\<forall>x. length(inouts\<^sub>v x) = m - Suc 0 \<and> length(inouts\<^sub>v' x) = n - Suc 0 \<and> 
             f_PostFD o1 (f (f_PreFD (xx inouts\<^sub>v) i1 inouts\<^sub>v)) x = inouts\<^sub>v' x) \<and>
            (\<forall>x xa. length(x xa) = m - Suc 0 \<longrightarrow> length(f_PostFD o1 (f (f_PreFD (xx x) i1 x)) xa) = n - Suc 0)"
          apply (rule conjI)
          using 2 a1 apply simp
          apply (rule allI)
          apply (clarify)
          proof -
            fix x::"nat \<Rightarrow> real list" and xa::nat
            assume a11: "length (x xa) = m - Suc 0"
            have 1: "length((f_PreFD (xx x) i1 x) xa) = m"
              using a11 apply (simp add: f_PreFD_def)
              using i1_lt_m by linarith
            have 2: "length((f (f_PreFD (xx x) i1 x)) xa) = n"
              using "1" SimBlock_FBlock_fn s1 by blast
            show "length(f_PostFD o1 (f (f_PreFD (xx x) i1 x)) xa) = n - Suc 0"
              apply (simp add: f_PostFD_def f_PreFD_def)
              using 1 2 o1_lt_n by linarith
          qed
      next
        fix ok\<^sub>v inouts\<^sub>v ok\<^sub>v' inouts\<^sub>v'
        assume a1: "\<forall>x. length(inouts\<^sub>v x) = m - Suc 0 \<and> length(inouts\<^sub>v' x) = n - Suc 0 \<and> 
                    f_PostFD o1 (f (f_PreFD (xx inouts\<^sub>v) i1 inouts\<^sub>v)) x = inouts\<^sub>v' x"
        assume a2: "\<forall>x xa. length(x xa) = m - Suc 0 \<longrightarrow> length(f_PostFD o1 (f (f_PreFD (xx x) i1 x)) xa) = n - Suc 0"
        have 1: "\<forall>x. length(inouts\<^sub>v x) = m - Suc 0"
          using a1 by simp
        have 2: "xx inouts\<^sub>v = (Solution i1 o1 m n f inouts\<^sub>v)"
          apply (rule unique_solution)
          using s2 apply (simp)
          using s3 apply (simp)
          using 1 by (simp)
        show "(\<forall>x. length(inouts\<^sub>v x) = m - Suc 0 \<and>  length(inouts\<^sub>v' x) = n - Suc 0 \<and> 
            f_PostFD o1 (f (f_PreFD (Solution i1 o1 m n f inouts\<^sub>v) i1 inouts\<^sub>v)) x = inouts\<^sub>v' x) \<and>
            (\<forall>x xa. length(x xa) = m - Suc 0 \<longrightarrow> 
              length(f_PostFD o1 (f (f_PreFD (Solution i1 o1 m n f x) i1 x)) xa) = n - Suc 0)"
          apply (rule conjI)
          using 2 a1 apply auto[1]
          apply (rule allI)
          apply (clarify)
          proof -
            fix x::"nat \<Rightarrow> real list" and xa::nat
            assume a11: "length (x xa) = m - Suc 0"
            have 1: "length((f_PreFD (Solution i1 o1 m n f x) i1 x) xa) = m"
              using a11 apply (simp add: f_PreFD_def)
              using i1_lt_m by linarith
            have 2: "length((f (f_PreFD (Solution i1 o1 m n f x) i1 x)) xa) = n"
              using "1" SimBlock_FBlock_fn s1 by blast
            show "length(f_PostFD o1 (f (f_PreFD (Solution i1 o1 m n f x) i1 x)) xa) = n - Suc 0"
              apply (simp add: f_PostFD_def f_PreFD_def)
              using 1 2 o1_lt_n by linarith
          qed
      qed
  qed

lemma FBlock_feedback_ref:
  assumes s1: "SimBlock m n (FBlock (\<lambda>x n. True) m n f)"
  assumes s2: "Solvable i1 o1 m n (f)"
  shows "(FBlock (\<lambda>x n. True) m n f) f\<^sub>D (i1, o1) 
       \<sqsubseteq> (FBlock (\<lambda>x n. True) (m-1) (n-1)
            (\<lambda>x na. ((f_PostFD o1) o f o (f_PreFD (Solution i1 o1 m n f x) i1)) x na))"
  proof -
    have inps_1: "inps (FBlock (\<lambda>x n. True) m n f) = m"
      using s1 by (simp add: inps_P)
    have outps_1: "outps (FBlock (\<lambda>x n. True) m n f) = n"
      using s1 by (simp add: outps_P)
    have i1_lt_m: "i1 < m" 
      using s2 by (simp add: Solvable_def)
    have o1_lt_n: "o1 < n" 
      using s2 by (simp add: Solvable_def)
    have 1: "(FBlock (\<lambda>x n. True) m n f) f\<^sub>D (i1, o1) = (true \<turnstile>\<^sub>n (\<^bold>\<exists> x \<bullet> 
            (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m - Suc 0\<guillemotright> \<and>
                    #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m\<guillemotright> \<and> $inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>f_PreFD x i1\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>n\<guillemotright>)\<^sub>a) ;;
            ((\<^bold>\<forall> na \<bullet> #\<^sub>u($inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m\<guillemotright> \<and>
                      #\<^sub>u($inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> \<guillemotleft>f\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>na\<guillemotright>)\<^sub>a =\<^sub>u $inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a) \<and>
             (\<^bold>\<forall> x \<bullet> \<^bold>\<forall> na \<bullet> #\<^sub>u(\<guillemotleft>x na\<guillemotright>) =\<^sub>u \<guillemotleft>m\<guillemotright> \<Rightarrow> #\<^sub>u(\<guillemotleft>f x na\<guillemotright>) =\<^sub>u \<guillemotleft>n\<guillemotright>)) ;;
            (\<^bold>\<forall> na \<bullet> #\<^sub>u($inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and>
                     #\<^sub>u($inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n - Suc 0\<guillemotright> \<and>
                     $inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>f_PostFD o1\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>na\<guillemotright>)\<^sub>a \<and>
                     \<guillemotleft>uapply\<guillemotright>($inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a)\<^sub>a(\<guillemotleft>o1\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>x na\<guillemotright>)))"
      apply (simp add: inps_1 outps_1)
      apply (simp add: PreFD_def PostFD_def FBlock_def Solution_def)
      apply (simp add: ndesign_composition_wp wp_upred_def)
      by (rel_simp)
    have 2: "(true \<turnstile>\<^sub>n (\<^bold>\<exists> x \<bullet> 
            (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m - Suc 0\<guillemotright> \<and>
                    #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m\<guillemotright> \<and> $inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>f_PreFD x i1\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>n\<guillemotright>)\<^sub>a) ;;
            ((\<^bold>\<forall> na \<bullet> #\<^sub>u($inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m\<guillemotright> \<and>
                      #\<^sub>u($inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> \<guillemotleft>f\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>na\<guillemotright>)\<^sub>a =\<^sub>u $inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a) \<and>
             (\<^bold>\<forall> x \<bullet> \<^bold>\<forall> na \<bullet> #\<^sub>u(\<guillemotleft>x na\<guillemotright>) =\<^sub>u \<guillemotleft>m\<guillemotright> \<Rightarrow> #\<^sub>u(\<guillemotleft>f x na\<guillemotright>) =\<^sub>u \<guillemotleft>n\<guillemotright>)) ;;
            (\<^bold>\<forall> na \<bullet> #\<^sub>u($inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n\<guillemotright> \<and>
                     #\<^sub>u($inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n - Suc 0\<guillemotright> \<and>
                     $inouts\<acute>(\<guillemotleft>na\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>f_PostFD o1\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>na\<guillemotright>)\<^sub>a \<and>
                     \<guillemotleft>uapply\<guillemotright>($inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a)\<^sub>a(\<guillemotleft>o1\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>x na\<guillemotright>)))
      \<sqsubseteq> (FBlock (\<lambda>x n. True) (m-1) (n-1)
            (\<lambda>x na. ((f_PostFD o1) o f o (f_PreFD (Solution i1 o1 m n f x) i1)) x na))"
      apply (simp add: FBlock_def Solution_def)
      apply (rule ndesign_refine_intro, simp+)
      apply (rel_simp)
      apply (rule_tac x = "(SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1))" in exI)
      apply (rule_tac x = "\<lambda>na. f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) 
                                        i1 inouts\<^sub>v na" in exI, simp)
      apply (rule conjI)
      apply (simp add: f_PreFD_def)
      using i1_lt_m apply linarith
      apply (rule_tac x = "\<lambda>na. (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1))
                                             i1 inouts\<^sub>v) na)" in exI, simp)
      apply (rule conjI)
      apply (simp add: f_PreFD_def)
      apply (rule conjI)
      using i1_lt_m apply linarith
      (* using SimBlock_FBlock_fn s1 apply blast*)
      defer
      apply (rule conjI)
      using SimBlock_FBlock_fn s1 apply blast
      apply (rule allI, rule conjI)
      (* using SimBlock_FBlock_fn s1 apply blast *)
      defer
      proof -
        fix inouts\<^sub>v::"nat \<Rightarrow> real list" and inouts\<^sub>v'::"nat \<Rightarrow> real list" and x::nat
        assume a1: "\<forall>x. length(inouts\<^sub>v x) = m - Suc 0 \<and>
           length(inouts\<^sub>v' x) = n - Suc 0 \<and>
           f_PostFD o1 (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v)) x = inouts\<^sub>v' x"
        let ?P= "\<lambda>xx.  \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)"
        have 1: "(?P (SOME xx. ?P xx))"
          apply (rule someI_ex[of "?P"])
          using s2 apply (simp add: Solvable_def)
          using a1 by blast
        show "f (f_PreFD (SOME xx. ?P xx) i1 inouts\<^sub>v) x!(o1) = (SOME xx. ?P xx) x"
          by (simp add: "1")
      next 
        fix inouts\<^sub>v inouts\<^sub>v'
        assume a1: "\<forall>x. length(inouts\<^sub>v x) = m - Suc 0 \<and>
           length(inouts\<^sub>v' x) = n - Suc 0 \<and>
           f_PostFD o1 (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v)) x =
           inouts\<^sub>v' x"
        assume a2: "\<forall>x xa. length(x xa) = m - Suc 0 \<longrightarrow>
              length(f_PostFD o1 (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 x) n!(o1)) i1 x)) xa) =
              n - Suc 0"
        from a1 have a1': "\<forall>x. length(inouts\<^sub>v x) = m - Suc 0"
          by (simp)
        have "\<forall>na. length((f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v) na) = m"
          using a1' f_PreFD_def apply (simp)
          using i1_lt_m by linarith
        then show "\<forall>x. length(f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v) x) = n"
          using SimBlock_FBlock_fn s1 by blast
      next
        fix inouts\<^sub>v inouts\<^sub>v' x
        assume a1: "\<forall>x. length(inouts\<^sub>v x) = m - Suc 0 \<and>
           length(inouts\<^sub>v' x) = n - Suc 0 \<and>
           f_PostFD o1 (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v)) x =
           inouts\<^sub>v' x"
        assume a2: "\<forall>x xa. length(x xa) = m - Suc 0 \<longrightarrow>
              length(f_PostFD o1 (f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 x) n!(o1)) i1 x)) xa) =
              n - Suc 0"
        from a1 have a1': "\<forall>x. length(inouts\<^sub>v x) = m - Suc 0"
          by (simp)
        have "\<forall>na. length((f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v) na) = m"
          using a1' f_PreFD_def apply (simp)
          using i1_lt_m by linarith
        then show "length(f (f_PreFD (SOME xx. \<forall>n. xx n = f (f_PreFD xx i1 inouts\<^sub>v) n!(o1)) i1 inouts\<^sub>v) x) = n"
          using SimBlock_FBlock_fn s1 by blast
      qed
    show ?thesis
      by (metis "1" "2")
  qed

lemma SimBlock_FBlock_feedback [simblock_healthy]:
  assumes s1: "SimBlock m n (FBlock (\<lambda>x n. True) m n f)"
  assumes s2: "Solvable i1 o1 m n (f)"
  shows "SimBlock (m-1) (n-1) ((FBlock (\<lambda>x n. True) m n f) f\<^sub>D (i1, o1))"
  proof -
    have m1_ge_0: "(m - (Suc 0)) \<ge> 0"
      using s2 by (simp add: Solvable_def)
    have m1_gt_0: "m > 0"
      using s2 by (simp add: Solvable_def)
    have inps_1: "inps (FBlock (\<lambda>x n. True) m n f) = m"
      using inps_outps s1 by blast
    have outps_1: "outps (FBlock (\<lambda>x n. True) m n f) = n"
      using inps_outps s1 by blast
    have i1_le_m: "i1 \<le> m - Suc 0"
      using s2 apply (simp add: Solvable_def)
      by linarith
    have o1_le_n: "o1 \<le> n - Suc 0"
      using s2 apply (simp add: Solvable_def)
      by linarith
    obtain inouts\<^sub>0::"nat \<Rightarrow> real list" where P0: "\<forall>x. length(inouts\<^sub>0 x) = (m - 1)"
      using m1_gt_0 list_len_avail
      by blast
    have "(\<forall>inouts\<^sub>0. (\<forall>x. length(inouts\<^sub>0 x) = (m-1))
        \<longrightarrow> (\<exists>xx.
          (\<forall>n. (xx n = 
                (f (\<lambda>n1. 
                    ((take i1 (inouts\<^sub>0 n1))@(xx n1)#(drop i1 (inouts\<^sub>0 n1)))
                   ) n)!o1
               )
          )))"
      using s2 by (simp add: Solvable_def f_PreFD_def)
    then have 1: "\<exists>xx. (\<forall>n. (xx n = (f (\<lambda>n1. ((take i1 (inouts\<^sub>0 n1))@(xx n1)#(drop i1 (inouts\<^sub>0 n1)))) n)!o1))"
      apply (simp)
      using P0 by simp
    obtain xx::"nat \<Rightarrow> real" 
    where P1: "(\<forall>n. (xx n = (f (\<lambda>n1. ((take i1 (inouts\<^sub>0 n1))@(xx n1)#(drop i1 (inouts\<^sub>0 n1)))) n)!o1
           ))"
      using 1 P0 by blast
    have 2: "Suc (m - Suc 0) = m"
      using m1_gt_0 by simp
    show ?thesis
      apply (simp add: SimBlock_def inps_1 outps_1 PreFD_def PostFD_def)
      apply (simp add: FBlock_def)
      apply (rel_auto)
      apply (simp add: f_blocks)
      (* apply (simp add: i1_le_m o1_le_n) *)
      apply (rule_tac x = "inouts\<^sub>0" in exI)
      apply (rule_tac x = "\<lambda>na. 
          (remove_at (f (\<lambda>n1. ((take i1 (inouts\<^sub>0 n1))@[xx n1]@(drop i1 (inouts\<^sub>0 n1)))) na) o1)" in exI)
      apply (rule_tac x = "xx" in exI)
      apply (rule_tac x = "True" in exI, simp)
      apply (rule_tac x = "\<lambda>na. (
          (\<lambda>n1. ((take i1 (inouts\<^sub>0 n1))@[xx n1]@(drop i1 (inouts\<^sub>0 n1)))) na)" in exI)
      apply (simp)
      apply (rule conjI)
      apply (rule allI)
      apply (rule conjI)
      using P0 apply (simp)
      apply (simp add: "2" P0)
      apply (rule_tac x = "True" in exI, simp) 
      apply (rule_tac x = "\<lambda>na. 
          ((f (\<lambda>n1. ((take i1 (inouts\<^sub>0 n1))@[xx n1]@(drop i1 (inouts\<^sub>0 n1)))) na))" in exI)
      apply (simp)
      apply (rule conjI)
      using "2" P0 SimBlock_FBlock_fn s1 
      apply (smt One_nat_def add_Suc_right append_take_drop_id length_Cons length_append)
      apply (rule conjI)
      using SimBlock_FBlock_fn s1 apply blast
      apply (rule allI)
      apply (rule conjI)
      using SimBlock_FBlock_fn s1
      apply (smt "2" One_nat_def P0 add_Suc_right append_take_drop_id length_Cons length_append)
      apply (rule conjI)
      defer
      using P1 apply metis
      proof -
        fix x 
        have 1: "length(f (\<lambda>n1. take i1 (inouts\<^sub>0 n1) @ xx n1 # drop i1 (inouts\<^sub>0 n1)) x) = n"
          using "2" P0 SimBlock_FBlock_fn s1 
          by (smt One_nat_def add_Suc_right append_take_drop_id length_Cons length_append)
        show "min (length(f (\<lambda>n1. take i1 (inouts\<^sub>0 n1) @ xx n1 # drop i1 (inouts\<^sub>0 n1)) x)) o1 +
          (length(f (\<lambda>n1. take i1 (inouts\<^sub>0 n1) @ xx n1 # drop i1 (inouts\<^sub>0 n1)) x) - Suc o1) =
            n - Suc 0"
          apply (simp add: 1)
          using o1_le_n by linarith 
      qed
  qed

subsubsection {* Split *}
lemma SimBlock_Split2 [simblock_healthy]:
  "SimBlock 1 2 (Split2)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (simp add: f_blocks)
  apply (rule_tac x = "\<lambda>na. [1]" in exI)
  apply force
  by (simp add: f_blocks)

subsection {* Blocks *}
subsubsection {* Source *}
paragraph {* Const *}
lemma SimBlock_Const [simblock_healthy]:
  "SimBlock 0 1 (Const c0)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (simp add: f_blocks)
  apply (rule_tac x = "\<lambda>na. []" in exI)
  apply force
  by (simp add: f_blocks)

paragraph {* Pulse Generator *}

subsubsection {* Unit Delay *}
lemma SimBlock_UnitDelay [simblock_healthy]:
  "SimBlock 1 1 (UnitDelay x0)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (simp add: f_blocks)
  apply (rule_tac x = "\<lambda>na. [1]" in exI)
  apply (rule_tac x = "\<lambda>na. [if na = 0 then x0 else 1]" in exI)
  apply (simp)
  by (simp add: f_blocks)

subsubsection {* Discrete-Time Integrator *}

subsubsection {* Sum *}
lemma SimBlock_Sum2 [simblock_healthy]:
  "SimBlock 2 1 (Sum2)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (simp add: f_blocks)
  apply (rule_tac x = "\<lambda>na. [1,1]" in exI)
  apply (rule_tac x = "\<lambda>na. [2]" in exI)
  apply (simp)
  by (simp add: f_blocks)

subsubsection {* Product *}
lemma SimBlock_Mul2 [simblock_healthy]:
  "SimBlock 2 1 (Mul2)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (simp add: f_blocks)
  apply (rule_tac x = "\<lambda>na. [1,1]" in exI)
  apply (rule_tac x = "\<lambda>na. [1]" in exI)
  apply (simp)
  by (simp add: f_blocks)

lemma SimBlock_Div2 [simblock_healthy]:
  "SimBlock 2 1 (Div2)"
  apply (simp add: f_sim_blocks)
  apply (simp add: SimBlock_def FBlock_def)
  apply (rel_auto)
  apply (rule_tac x = "\<lambda>na. [1,1]" in exI)
  apply (simp)
  apply (rule conjI)
  apply (rule_tac x = "\<lambda>na. [1]" in exI)
  apply (simp add: f_blocks)
  by (simp add: f_blocks)

subsubsection {* Gain *}
lemma SimBlock_Gain [simblock_healthy]:
  "SimBlock 1 1 (Gain k)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (simp add: f_blocks)
  apply (rule_tac x = "\<lambda>na. [1]" in exI)
  apply (rule_tac x = "\<lambda>na. [k]" in exI)
  apply (simp)
  by (simp add: f_blocks)

subsubsection {* Saturation *}
lemma SimBlock_Limit [simblock_healthy]:
  assumes "ymin \<le> ymax"
  shows "SimBlock 1 1 (Limit ymin ymax)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (simp add: f_blocks)
  apply (rule_tac x = "\<lambda>na. [ymin]" in exI)
  apply (rule_tac x = "\<lambda>na. [ymin]" in exI)
  using assms apply (simp)
  by (simp add: f_blocks)

subsubsection {* MinMax *}
lemma SimBlock_Min2 [simblock_healthy]:
  shows "SimBlock 2 1 (Min2)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (simp add: f_blocks)
  apply (rule_tac x = "\<lambda>na. [1,2]" in exI)
  apply (rule_tac x = "\<lambda>na. [1]" in exI)
  apply (simp)
  by (simp add: f_blocks)

lemma SimBlock_Max2 [simblock_healthy]:
  shows "SimBlock 2 1 (Max2)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (simp add: f_blocks)
  apply (rule_tac x = "\<lambda>na. [1,2]" in exI)
  apply (rule_tac x = "\<lambda>na. [2]" in exI)
  apply (simp)
  by (simp add: f_blocks)

subsubsection {* Rounding *}
lemma SimBlock_RoundFloor [simblock_healthy]:
  shows "SimBlock 1 1 (RoundFloor)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (simp add: f_blocks)
  apply (rule_tac x = "\<lambda>na. [1]" in exI)
  apply (rule_tac x = "\<lambda>na. [1]" in exI)
  apply auto[1]
  by (simp add: f_blocks)

lemma SimBlock_RoundCeil [simblock_healthy]:
  shows "SimBlock 1 1 (RoundCeil)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (simp add: f_blocks)
  apply (rule_tac x = "\<lambda>na. [1]" in exI)
  apply (rule_tac x = "\<lambda>na. [1]" in exI)
  apply auto[1]
  by (simp add: f_blocks)

subsubsection {* Combinatorial Logic *}

subsubsection {* Logic Operators *}
paragraph {* AND *}
lemma "LAnd [1,1] = True"
  by auto

lemma "LAnd [1,1,0] = False"
  by auto

lemma LAnd_and_not: "LAnd [a,b] = (a \<noteq> 0 \<and> b \<noteq> 0)"
  by (simp)

lemma LAnd_not_or: "LAnd [a,b] = (\<not> (a = 0 \<or> b = 0))"
  by (simp)

lemma SimBlock_LopAND [simblock_healthy]:
  assumes s1: "m > 0"
  shows "SimBlock m 1 (LopAND m)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  proof -
    obtain inouts\<^sub>v::"nat \<Rightarrow> real list" 
    where P: "\<forall>na. length(inouts\<^sub>v na) = m \<and> (\<forall>x<m. ((inouts\<^sub>v na)!x = 0))"
      using list_len_avail' by fastforce
    have 1: "(\<forall>x<m. ((inouts\<^sub>v na)!x = 0))"
      using P by blast
    have 2: "length(inouts\<^sub>v na) = m"
      using P by blast
    from 1 2 have 3: "(LAnd (inouts\<^sub>v x) = False)"
      using P s1 by (metis LAnd.simps(2) hd_Cons_tl length_0_conv neq0_conv nth_Cons_0)
    show "\<exists>inouts\<^sub>v inouts\<^sub>v'.
       \<forall>x. length(inouts\<^sub>v' x) = Suc 0 \<and> length(inouts\<^sub>v x) = m \<and> f_LopAND inouts\<^sub>v x = inouts\<^sub>v' x"
      apply (rule_tac x = "inouts\<^sub>v" in exI)
      apply (simp add: f_blocks)
      apply (rule_tac x = "\<lambda>na. [0]" in exI)
      using P 3 
      by (metis (full_types) LAnd.simps(2) hd_Cons_tl length_0_conv length_Cons nth_Cons_0 s1)
  next
    show "\<forall>x na. length(x na) = m \<longrightarrow> length(f_LopAND x na) = Suc 0"
      by (simp add: f_blocks)
  qed

paragraph {* OR *}
lemma "LOr [0,0] = False"
  by auto

lemma "LOr [0,1,0] = True"
  by auto

lemma SimBlock_LopOR [simblock_healthy]:
  assumes s1: "m > 0"
  shows "SimBlock m 1 (LopOR m)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  proof -
    obtain inouts\<^sub>v::"nat \<Rightarrow> real list" 
    where P: "\<forall>na. length(inouts\<^sub>v na) = m \<and> (\<forall>x<m. ((inouts\<^sub>v na)!x = 1))"
      using list_len_avail' by fastforce
    have 1: "(\<forall>x<m. ((inouts\<^sub>v na)!x = 1))"
      using P by blast
    have 2: "length(inouts\<^sub>v na) = m"
      using P by blast
    from 1 2 have 3: "(LOr (inouts\<^sub>v x) = True)"
      using P s1
      by (metis LOr.elims(3) length_0_conv neq0_conv nth_Cons_0 zero_neq_one)
    show "\<exists>inouts\<^sub>v inouts\<^sub>v'.
       \<forall>x. length(inouts\<^sub>v' x) = Suc 0 \<and> length(inouts\<^sub>v x) = m \<and> f_LopOR inouts\<^sub>v x = inouts\<^sub>v' x"
      apply (rule_tac x = "inouts\<^sub>v" in exI)
      apply (simp add: f_blocks)
      apply (rule_tac x = "\<lambda>na. [1]" in exI)
      using P 3 
      by (metis (full_types) LOr.simps(2) hd_Cons_tl length_0_conv length_Cons nth_Cons_0 s1)
  next
    show "\<forall>x na. length(x na) = m \<longrightarrow> length(f_LopOR x na) = Suc 0"
      by (simp add: f_blocks)
  qed

paragraph {* NAND *}
lemma "LNand [1,1] = False"
  by auto

lemma "LNand [1,1,0] = True"
  by auto

lemma SimBlock_LopNAND [simblock_healthy]:
  assumes s1: "m > 0"
  shows "SimBlock m 1 (LopNAND m)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  proof -
    obtain inouts\<^sub>v::"nat \<Rightarrow> real list" 
    where P: "\<forall>na. length(inouts\<^sub>v na) = m \<and> (\<forall>x<m. ((inouts\<^sub>v na)!x = 0))"
      using list_len_avail' by fastforce
    have 1: "(\<forall>x<m. ((inouts\<^sub>v na)!x = 0))"
      using P by blast
    have 2: "length(inouts\<^sub>v na) = m"
      using P by blast
    from 1 2 have 3: "(LNand (inouts\<^sub>v x) = True)"
      using P s1
      by (metis LNand.elims(3) length_0_conv neq0_conv nth_Cons_0)
    show "\<exists>inouts\<^sub>v inouts\<^sub>v'.
       \<forall>x. length(inouts\<^sub>v' x) = Suc 0 \<and> length(inouts\<^sub>v x) = m \<and> f_LopNAND inouts\<^sub>v x = inouts\<^sub>v' x"
      apply (rule_tac x = "inouts\<^sub>v" in exI)
      apply (simp add: f_blocks)
      apply (rule_tac x = "\<lambda>na. [1]" in exI)
      using P 3 
      by (metis (full_types) LNand.simps(2) hd_Cons_tl length_0_conv length_Cons nth_Cons_0 s1)
  next
    show "\<forall>x na. length(x na) = m \<longrightarrow> length(f_LopNAND x na) = Suc 0"
      by (simp add: f_blocks)
  qed

paragraph {* NOR *}
lemma "LNor [1,0] = False"
  by auto

lemma "LNor [0,0,0] = True"
  by auto

paragraph {* XOR *}
lemma "LXor [1,0] 0 = True"
  by auto

lemma "LXor [1,0,1] 0 = False"
  by auto

paragraph {* NXOR *}
lemma "LNxor [1,0] 0 = False"
  by auto

lemma "LNxor [1,0,1] 0 = True"
  by auto

paragraph {* NOT *}
lemma SimBlock_LopNOT [simblock_healthy]:
  shows "SimBlock 1 1 (LopNOT)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [0]" in exI)
  apply (rule_tac x = "\<lambda>na. [1]" in exI)
  apply (simp add: f_LopNOT_def)
  by (simp add: f_blocks)

subsubsection {* Relational Operator *}

paragraph {* Equal == *}
lemma SimBlock_RopEQ [simblock_healthy]:
  shows "SimBlock 2 1 (RopEQ)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [0,0]" in exI)
  apply (rule_tac x = "\<lambda>na. [1]" in exI)
  apply (simp add: f_RopEQ_def)
  by (simp add: f_blocks)

paragraph {* Notequal ~= *}
lemma SimBlock_RopNEQ [simblock_healthy]:
  shows "SimBlock 2 1 (RopNEQ)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [0,0]" in exI)
  apply (rule_tac x = "\<lambda>na. [0]" in exI)
  apply (simp add: f_RopNEQ_def)
  by (simp add: f_blocks)

paragraph {* Less Than < *}
lemma SimBlock_RopLT [simblock_healthy]:
  shows "SimBlock 2 1 (RopLT)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [0,0]" in exI)
  apply (rule_tac x = "\<lambda>na. [0]" in exI)
  apply (simp add: f_RopLT_def)
  by (simp add: f_blocks)

paragraph {* Less Than or Equal to <= *}
lemma SimBlock_RopLE [simblock_healthy]:
  shows "SimBlock 2 1 (RopLE)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [0,0]" in exI)
  apply (rule_tac x = "\<lambda>na. [1]" in exI)
  apply (simp add: f_blocks)
  by (simp add: f_blocks)

paragraph {* Greater Than > *}
lemma SimBlock_RopGT [simblock_healthy]:
  shows "SimBlock 2 1 (RopGT)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [0,0]" in exI)
  apply (rule_tac x = "\<lambda>na. [0]" in exI)
  apply (simp add: f_blocks)
  by (simp add: f_blocks)

paragraph {* Greater Than or Equal to >= *}
lemma SimBlock_RopGE [simblock_healthy]:
  shows "SimBlock 2 1 (RopGE)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [0,0]" in exI)
  apply (rule_tac x = "\<lambda>na. [1]" in exI)
  apply (simp add: f_blocks)
  by (simp add: f_blocks)

subsubsection {* Switch *}
lemma SimBlock_Switch1 [simblock_healthy]:
  shows "SimBlock 3 1 (Switch1 th)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [0,th,1]" in exI)
  apply (rule_tac x = "\<lambda>na. [0]" in exI)
  apply (simp add: f_blocks)
  by (simp add: f_blocks)

lemma SimBlock_Switch2 [simblock_healthy]:
  shows "SimBlock 3 1 (Switch2 th)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [0,th+1,1]" in exI)
  apply (rule_tac x = "\<lambda>na. [0]" in exI)
  apply (simp add: f_blocks)
  by (simp add: f_blocks)

lemma SimBlock_Switch3 [simblock_healthy]:
  shows "SimBlock 3 1 (Switch3)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [0,1,1]" in exI)
  apply (rule_tac x = "\<lambda>na. [0]" in exI)
  apply (simp add: f_blocks)
  by (simp add: f_blocks)

subsubsection {* Merge *}

subsubsection {* Subsystem *}

subsubsection {* Enabled Subsystem *}

subsubsection {* Triggered Subsystem *}

subsubsection {* Enabled and Triggered Subsystem *}

subsubsection {* Data Type Conversion *}
lemma SimBlock_DataTypeConvUint32Zero [simblock_healthy]:
  shows "SimBlock 1 1 (DataTypeConvUint32Zero)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [3294967295.5]" in exI)
  apply (rule_tac x = "\<lambda>na. [3294967295]" in exI)
  apply (simp add: f_blocks RoundZero_def uint32_def)
  by (simp add: f_blocks)

lemma SimBlock_DataTypeConvInt32Zero [simblock_healthy]:
  shows "SimBlock 1 1 (DataTypeConvInt32Zero)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [-4.5]" in exI)
  apply (rule_tac x = "\<lambda>na. [-4]" in exI)
  apply (simp add: f_blocks RoundZero_def int32_def)
  by (simp add: f_blocks)

subsubsection {* Initial Condition (IC) *}
lemma SimBlock_IC [simblock_healthy]:
  shows "SimBlock 1 1 (IC x0)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [x0]" in exI)
  apply (rule_tac x = "\<lambda>na. [x0]" in exI)
  apply (simp add: f_blocks)
  by (simp add: f_blocks)

subsubsection {* Router Block *}
lemma assembleOutput_len: 
  "\<forall>x na. length(assembleOutput (x na) routes) = length(routes)"
  apply (auto)
  proof (induction routes)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a routes)
    then show ?case
      by (simp)
  qed

lemma SimBlock_Router [simblock_healthy]:
  assumes s1: "length(routes) = m"
  shows "SimBlock m m (Router m routes)"
  apply (simp add: f_sim_blocks)
  apply (rule SimBlock_FBlock)
  proof -
    obtain inouts\<^sub>v::"nat \<Rightarrow> real list" 
    where P: "\<forall>na. length(inouts\<^sub>v na) = m \<and> (\<forall>x<m. ((inouts\<^sub>v na)!x = 0))"
      using list_len_avail' by fastforce
    have 1: "(\<forall>x<m. ((inouts\<^sub>v na)!x = 0))"
      using P by blast
    have 2: "length(inouts\<^sub>v na) = m"
      using P by blast
    have 3: "\<forall>x. length(assembleOutput (inouts\<^sub>v x) routes) = length(routes)"
      by (simp add: assembleOutput_len)
    then have 4: "\<forall>x. length(assembleOutput (inouts\<^sub>v x) routes) = m"
      using s1 by simp
    show "\<exists>inouts\<^sub>v inouts\<^sub>v'.
       \<forall>x. length(inouts\<^sub>v' x) = m \<and> length(inouts\<^sub>v x) = m \<and> f_Router routes inouts\<^sub>v x = inouts\<^sub>v' x"
      apply (rule_tac x = "inouts\<^sub>v" in exI)
      apply (rule_tac x = "f_Router routes inouts\<^sub>v" in exI)
      apply (simp add: f_blocks)
      using 4 s1
      by (simp add: P)
  next
    show "\<forall>x na. length(x na) = m \<longrightarrow> length(f_Router routes x na) = m"
      apply (simp add: f_blocks)
      using s1 by (simp add: assembleOutput_len)
  qed

subsection {* Frequently Used Composition of Blocks *}

lemma UnitDelay_Id_parallel_comp: 
  "(UnitDelay 0 \<parallel>\<^sub>B Id) = (FBlock (\<lambda>x n. True) (2) (2) 
        (\<lambda>x n. [if n = 0 then 0 else hd(x (n-1)), hd(tl(x n))]))"
  proof -
    have f1: "(UnitDelay 0 \<parallel>\<^sub>B Id) = (FBlock (\<lambda>x n. True) (2) (2) 
        (\<lambda>x n. ((((f_UnitDelay 0) \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) 
             @ ((f_Id \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)))"
      using SimBlock_UnitDelay SimBlock_Id apply (simp add: FBlock_parallel_comp f_sim_blocks)
      by (simp add: numeral_2_eq_2)
    then have f1_0: "... = (FBlock (\<lambda>x n. True) (2) (2) 
        (\<lambda>x n. [if n = 0 then 0 else hd(x (n-1)), hd(tl(x n))]))"
      proof - 
        have "\<forall>(f::nat \<Rightarrow> real list) (n::nat). 
          ((\<lambda>x n. ((((f_UnitDelay 0) \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) 
             @ ((f_Id \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)) f n =  
            ((\<lambda>x n. [if n = 0 then 0 else hd(x (n-1)), hd(tl(x n))]) f n))"
          using f_Id_def f_UnitDelay_def apply (simp)
          by (metis drop_0 drop_Suc list.sel(1) take_Nil take_Suc)
        then show ?thesis
          by auto
      qed
    then show ?thesis
      by (simp add: f1 f1_0)
  qed

end
