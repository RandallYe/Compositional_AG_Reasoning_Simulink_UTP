section {* Simulink Blocks Examples *}

theory simu_contract_real_example
  imports
    simu_contract_real
begin

subsection {* inps and outps *}
lemma 
  fixes ok and inouts
  shows "\<lbrakk>(true \<turnstile>\<^sub>r II)\<rbrakk>\<^sub>e
   (\<lparr>ok\<^sub>v = ok, inouts\<^sub>v = inouts\<rparr>, \<lparr>ok\<^sub>v = ok, inouts\<^sub>v = inouts\<rparr>)"
  apply (rel_auto)
done

lemma 
  fixes ok and inouts
  assumes "\<lbrakk>(true \<turnstile>\<^sub>r II)\<rbrakk>\<^sub>e
   (\<lparr>ok\<^sub>v = ok, inouts\<^sub>v = inouts\<rparr>, \<lparr>ok\<^sub>v = ok1, inouts\<^sub>v = inouts\<rparr>)"
  shows "(ok1 = ok) \<or> \<not>ok"
  using assms apply (simp add: urel_defs)
  apply (rel_simp)
done

lemma 
  fixes ok and inouts
  assumes "\<lbrakk>(true \<turnstile>\<^sub>r II)\<rbrakk>\<^sub>e
   (\<lparr>ok\<^sub>v = ok, inouts\<^sub>v = inouts\<rparr>, \<lparr>ok\<^sub>v = ok1, inouts\<^sub>v = inouts\<rparr>)"
  shows "ok1 = ok"
  using assms apply (simp add: urel_defs)
  apply (rel_simp)
  (*
    "e": The prover derived "False" from "SimBlock_def", "impl_mp1", "inps_outps", "rdesign_post", "rdesign_pre", and "utp_pred_laws.inf_top_left", which could be due to a bug in Sledgehammer or to inconsistent axioms (including "sorry"s) 
    "z3": Timed out 
    "cvc4": Timed out 
    "spass": Timed out
  *)
sorry

declare [[show_types]]
lemma 
  fixes ok and inouts
  assumes "\<forall>x . length(inouts x) = Suc 0"
  shows "\<lbrakk>Id\<rbrakk>\<^sub>e
   (\<lparr>ok\<^sub>v = ok, inouts\<^sub>v = inouts\<rparr>, \<lparr>ok\<^sub>v = ok, inouts\<^sub>v = inouts\<rparr>)"
  apply (simp add: sim_blocks)
  apply (rel_simp)
  by (simp add: assms)

lemma 
  fixes ok and inouts
  assumes "\<forall>x . length(inouts x) = 2"
  shows "\<lbrakk>takem 2 1\<rbrakk>\<^sub>e
   (\<lparr>ok\<^sub>v = ok, inouts\<^sub>v = inouts\<rparr>, \<lparr>ok\<^sub>v = ok, inouts\<^sub>v = \<lambda>na . [hd(inouts na)]\<rparr>)"
  apply (simp add: sim_blocks)
  apply (rel_simp)
  by (metis assms length_0_conv take_0 take_Suc zero_not_eq_two)

lemma 
  fixes ok\<^sub>v0 and inouts\<^sub>v0
  assumes "\<forall>x . length(inouts\<^sub>v0 x) = (m1 + m2 + m3)"
  shows "\<lbrakk>takem (m1 + m2 + m3) (m1 + m2)\<rbrakk>\<^sub>e
          (\<lparr>ok\<^sub>v = ok\<^sub>v0, inouts\<^sub>v = inouts\<^sub>v0\<rparr>, \<lparr>ok\<^sub>v = ok\<^sub>v0, inouts\<^sub>v = \<lambda>na . take (m1+m2) (inouts\<^sub>v0 na)\<rparr>)"
  apply (simp add: sim_blocks)
  apply (rel_simp)
  using assms by auto

lemma 
  fixes m and n
  assumes a2: "n \<le> m"
  assumes a1: "\<lbrakk>takem m n\<rbrakk>\<^sub>e
          (\<lparr>ok\<^sub>v = ok\<^sub>v0, inouts\<^sub>v = inouts\<^sub>v0\<rparr>, \<lparr>ok\<^sub>v = ok\<^sub>v1, inouts\<^sub>v = inouts\<^sub>v1\<rparr>)"
  (* shows "(ok\<^sub>v0 \<longrightarrow> ok\<^sub>v1)"*)
  (* shows "(ok\<^sub>v1 = ok\<^sub>v0) \<or> ok\<^sub>v1)" *)
  shows "ok\<^sub>v0 \<longrightarrow> (\<forall>x . length(inouts\<^sub>v0 x) = (m))"
  proof -
    show ?thesis
      using a1 a2 apply (simp add: sim_blocks)
      apply (rel_simp)
    done
  qed

lemma 
  fixes m and n
  assumes a2: "n \<le> m"
  assumes a1: "\<lbrakk>takem m n\<rbrakk>\<^sub>e
          (\<lparr>ok\<^sub>v = ok\<^sub>v0, inouts\<^sub>v = inouts\<^sub>v0\<rparr>, \<lparr>ok\<^sub>v = ok\<^sub>v1, inouts\<^sub>v = inouts\<^sub>v1\<rparr>)"
  (* shows "(ok\<^sub>v0 \<longrightarrow> ok\<^sub>v1)"*)
  (* shows "(ok\<^sub>v1 = ok\<^sub>v0) \<or> ok\<^sub>v1)" *)
  shows "ok\<^sub>v0 \<and> n \<noteq> 0 \<longrightarrow> (inouts\<^sub>v1 = (\<lambda>na. (take n (inouts\<^sub>v0 na))))"
  proof -
    show ?thesis
      using a1 a2 apply (simp add: sim_blocks)
      apply (rel_simp)
      proof -
        fix x
        assume "\<forall>x::nat.
          length(inouts\<^sub>v0 x) = m \<and>
          length(inouts\<^sub>v1 x) = n \<and>
          \<lbrakk>bop op = (\<guillemotleft>take n\<guillemotright>($inouts(\<guillemotleft>x\<guillemotright>)\<^sub>a)\<^sub>a) ($inouts\<acute>(\<guillemotleft>x\<guillemotright>)\<^sub>a)\<rbrakk>\<^sub>e
           (get\<^bsub>\<Sigma>\<^sub>D \<times> \<Sigma>\<^sub>D\<^esub> (\<lparr>ok\<^sub>v = True, inouts\<^sub>v = inouts\<^sub>v0\<rparr>, \<lparr>ok\<^sub>v = True, inouts\<^sub>v = inouts\<^sub>v1\<rparr>))"
        show "inouts\<^sub>v1 x = take n (inouts\<^sub>v0 x)"
    done
  qed

lemma 
  fixes m and n
  assumes a2: "n \<le> m"
  assumes a1: "\<lbrakk>takem m n\<rbrakk>\<^sub>e
          (\<lparr>ok\<^sub>v = ok\<^sub>v0, inouts\<^sub>v = inouts\<^sub>v0\<rparr>, \<lparr>ok\<^sub>v = ok\<^sub>v1, inouts\<^sub>v = inouts\<^sub>v1\<rparr>)"
  (* shows "(ok\<^sub>v0 \<longrightarrow> ok\<^sub>v1)"*)
  (* shows "(ok\<^sub>v1 = ok\<^sub>v0) \<or> ok\<^sub>v1)" *)
  shows "ok\<^sub>v0 \<longrightarrow> (\<forall>x . length(inouts\<^sub>v1 x) = (n))"
  proof -
    show ?thesis
      using a1 a2 apply (simp add: sim_blocks)
      apply (rel_simp)
    done
  qed


subsubsection {* SimBlock *}
paragraph {* Illustration *}

lemma "(pre\<^sub>D(Id) \<and> post\<^sub>D(Id)) = 
  (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u 1 \<and> #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u 1 \<and> 
         head\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a))"
apply (simp add: sim_blocks)
done

lemma Dom_Id: "Dom(pre\<^sub>D(Id) \<and> post\<^sub>D(Id)) = (\<^bold>\<forall> n \<bullet> #\<^sub>u(&inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u 1)"
apply (simp add: sim_blocks Dom_def)
apply (rel_auto)
done

lemma Ran_Id: "Ran(pre\<^sub>D(Id) \<and> post\<^sub>D(Id)) = (\<^bold>\<forall> n \<bullet> #\<^sub>u(&inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u 1)"
apply (simp add: sim_blocks Ran_def)
apply (rel_auto)
done

lemma "(\<^bold>\<forall> n \<bullet> #\<^sub>u(&inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u 1) \<sqsubseteq> Dom(pre\<^sub>D(Id) \<and> post\<^sub>D(Id))"
apply (simp add: Dom_Id)
done

subsubsection {* inps and outps *}

subsection {* Experiments *}

paragraph {* Example *}
lemma takem_simp2:
"(takem (Suc (Suc 0)) (Suc 0)) ;; Id = 
 true \<turnstile>\<^sub>r (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>2\<guillemotright> \<and>
               #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>1\<guillemotright> \<and>
               head\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a))"
apply (simp add: sim_blocks)
apply (rel_auto)
apply (metis list.sel(1) list.size(3) numeral_2_eq_2 take_Suc zero_not_eq_two)
by (metis Cons_nth_drop_Suc Suc_1 Suc_leI append.simps(1) drop_0 drop_all hd_drop_conv_nth take_0 take_hd_drop zero_less_Suc)

lemma dropm_simp2:
"(dropm (Suc (Suc 0)) (Suc 0)) ;; Id = 
 true \<turnstile>\<^sub>r (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>2\<guillemotright> \<and>
               #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>1\<guillemotright> \<and>
               last\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a))"
apply (simp add: sim_blocks)
apply (rel_auto)
apply (metis One_nat_def add_Suc_right cancel_ab_semigroup_add_class.add_diff_cancel_left' hd_drop_conv_nth last_conv_nth lessI list.size(3) numeral_2_eq_2 of_nat_1 of_nat_Suc semiring_1_class.of_nat_0 zero_not_eq_two)
by (smt Cons_nth_drop_Suc One_nat_def Suc_less_eq add_2_eq_Suc add_Suc cancel_ab_semigroup_add_class.add_diff_cancel_left' drop_0 drop_all hd_drop_conv_nth last_conv_nth neq0_conv neq_Nil_conv not_less_zero numeral_2_eq_2 order_refl)

lemma lem_parallel_1 : "\<And>(ok\<^sub>v::bool) inouts\<^sub>v more (ok\<^sub>v'::bool) inouts\<^sub>v'.
       \<not> ok\<^sub>v \<Longrightarrow>
       \<exists>ok\<^sub>v inouts\<^sub>v'' morea ok\<^sub>v'' inouts\<^sub>v'''.
          (\<exists>inouts\<^sub>v. \<forall>x. inouts\<^sub>v''' x = inouts\<^sub>v x) \<and>
          (\<exists>ok\<^sub>v''' inouts\<^sub>v''''.
              (\<exists>inouts\<^sub>v. \<forall>x. inouts\<^sub>v'''' x = inouts\<^sub>v x) \<and>
              \<not> ok\<^sub>v \<and>
              (\<forall>x. inouts\<^sub>v'' x = inouts\<^sub>v x) \<and>
              morea = more \<and> ok\<^sub>v' = (ok\<^sub>v'' \<and> ok\<^sub>v''') \<and> (\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v''' x @ inouts\<^sub>v'''' x))"
proof -
  -- {* use fix to fix variables in \<And> *}
  fix ok\<^sub>v :: "bool" and 
      inouts\<^sub>v and 
      more and 
      ok\<^sub>v':: "bool" and 
      inouts\<^sub>v'
  assume "\<not> ok\<^sub>v"
  show "\<exists>ok1\<^sub>v inouts\<^sub>v'' morea ok\<^sub>v'' inouts\<^sub>v'''.
          (\<exists>inouts1\<^sub>v. \<forall>x. inouts\<^sub>v''' x = inouts1\<^sub>v x) \<and>
          (\<exists>ok\<^sub>v''' inouts\<^sub>v''''.
              (\<exists>inouts1\<^sub>v. \<forall>x. inouts\<^sub>v'''' x = inouts1\<^sub>v x) \<and>
              \<not> ok1\<^sub>v \<and>
              (\<forall>x. inouts\<^sub>v'' x = inouts\<^sub>v x) \<and>
              morea = more \<and>
              ok\<^sub>v' = (ok\<^sub>v'' \<and> ok\<^sub>v''') \<and> 
              (\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v''' x @ inouts\<^sub>v'''' x))"
  proof -
    -- {* use obtain to fix local variables in \<exists> *}
    obtain ok1\<^sub>v and inouts\<^sub>v'' and morea and ok\<^sub>v'' and inouts\<^sub>v''' 
    where p: "ok1\<^sub>v = ok\<^sub>v" and "inouts\<^sub>v'' = inouts\<^sub>v" and "morea = more" and "ok\<^sub>v''= ok\<^sub>v'" and
      "inouts\<^sub>v''' = inouts\<^sub>v'" 
      apply blast
    done
    (* P(x) *)
    have 1: "(\<exists>inouts1\<^sub>v. \<forall>x. inouts\<^sub>v' x = inouts1\<^sub>v x) \<and>
          (\<exists>ok\<^sub>v''' inouts\<^sub>v''''.
              (\<exists>inouts1\<^sub>v. \<forall>x. inouts\<^sub>v'''' x = inouts1\<^sub>v x) \<and>
              \<not> ok\<^sub>v \<and>
              (\<forall>x. inouts\<^sub>v x = inouts\<^sub>v x) \<and>
              more = more \<and>
              ok\<^sub>v' = (ok\<^sub>v' \<and> ok\<^sub>v''') \<and> 
              (\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v' x @ inouts\<^sub>v'''' x))"
      proof -
        have c1: "(\<exists>inouts1\<^sub>v. \<forall>x. inouts\<^sub>v' x = inouts1\<^sub>v x)" 
          by blast
        have c2: "(\<exists>ok\<^sub>v''' inouts\<^sub>v''''.
              (\<exists>inouts1\<^sub>v. \<forall>x. inouts\<^sub>v'''' x = inouts1\<^sub>v x) \<and>
              \<not> ok\<^sub>v \<and>
              (\<forall>x. inouts\<^sub>v x = inouts\<^sub>v x) \<and>
              more = more \<and>
              ok\<^sub>v' = (ok\<^sub>v' \<and> ok\<^sub>v''') \<and> 
              (\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v' x @ inouts\<^sub>v'''' x))"
          proof -
            obtain ok\<^sub>v''' and inouts\<^sub>v'''' where "ok\<^sub>v''' = ok\<^sub>v'" and "inouts\<^sub>v'''' = (\<lambda>x.[])"
              by auto
            have c3: "(\<exists>inouts1\<^sub>v. \<forall>x. [] = inouts1\<^sub>v x) \<and>
              \<not> ok\<^sub>v \<and>
              (\<forall>x. inouts\<^sub>v x = inouts\<^sub>v x) \<and>
              more = more \<and>
              ok\<^sub>v' = (ok\<^sub>v' \<and> ok\<^sub>v') \<and> 
              (\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v' x @ [])"
              using \<open>\<not> ok\<^sub>v\<close> by fastforce
            from c3 show ?thesis
              by metis
          qed
        from c1 and c2 show ?thesis
          by auto
      qed
    (* \<exists>x. P(x) *)
    then show ?thesis
      by metis
  qed
qed

text {* Parallel of two @{term "Id"}s equal to a @{term "Idm"} with two inputs and ouptuts. *}
lemma parallel_id_equal_idm2: "sim_parallel Id Id = Idm 2"
apply (simp add: sim_parallel_def inps_id mergeB_def par_by_merge_def)
apply (simp add: takem_simp2)
apply (simp add: dropm_simp2)
apply (simp add: Idm_def)
apply (simp add: U0_def U1_def)
apply (rel_auto+)
apply (metis Cons_nth_drop_Suc One_nat_def Suc_1 add.right_neutral add_Suc_right append.simps(1) append_Cons cancel_ab_semigroup_add_class.add_diff_cancel_left' drop_0 drop_all hd_drop_conv_nth last_conv_nth lessI neq0_conv neq_Nil_conv order_refl zero_neq_numeral)
-- {* Subgoal 2: *}
apply (simp add: lem_parallel_1)
proof -
  (*
  -- {* use fix to fix variables in \<And> *}
  fix ok\<^sub>v :: "bool" and 
      inouts\<^sub>v and 
      more and 
      ok\<^sub>v':: "bool" and 
      inouts\<^sub>v'
  assume "\<not> ok\<^sub>v"
  show "\<exists>ok1\<^sub>v inouts\<^sub>v'' morea ok\<^sub>v'' inouts\<^sub>v'''.
          (\<exists>inouts1\<^sub>v. \<forall>x. inouts\<^sub>v''' x = inouts1\<^sub>v x) \<and>
          (\<exists>ok\<^sub>v''' inouts\<^sub>v''''.
              (\<exists>inouts1\<^sub>v. \<forall>x. inouts\<^sub>v'''' x = inouts1\<^sub>v x) \<and>
              \<not> ok1\<^sub>v \<and>
              (\<forall>x. inouts\<^sub>v'' x = inouts\<^sub>v x) \<and>
              morea = more \<and>
              ok\<^sub>v' = (ok\<^sub>v'' \<and> ok\<^sub>v''') \<and> 
              (\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v''' x @ inouts\<^sub>v'''' x))"
  proof -
    -- {* use obtain to fix local variables in \<exists> *}
    obtain ok1\<^sub>v and inouts\<^sub>v'' and morea and ok\<^sub>v'' and inouts\<^sub>v''' 
    where p: "ok1\<^sub>v = ok\<^sub>v" and "inouts\<^sub>v'' = inouts\<^sub>v" and "morea = more" and "ok\<^sub>v''= ok\<^sub>v'" and
      "inouts\<^sub>v''' = inouts\<^sub>v'" 
      apply blast
    done
    (* P(x) *)
    have 1: "(\<exists>inouts1\<^sub>v. \<forall>x. inouts\<^sub>v' x = inouts1\<^sub>v x) \<and>
          (\<exists>ok\<^sub>v''' inouts\<^sub>v''''.
              (\<exists>inouts1\<^sub>v. \<forall>x. inouts\<^sub>v'''' x = inouts1\<^sub>v x) \<and>
              \<not> ok\<^sub>v \<and>
              (\<forall>x. inouts\<^sub>v x = inouts\<^sub>v x) \<and>
              more = more \<and>
              ok\<^sub>v' = (ok\<^sub>v' \<and> ok\<^sub>v''') \<and> 
              (\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v' x @ inouts\<^sub>v'''' x))"
      proof -
        have c1: "(\<exists>inouts1\<^sub>v. \<forall>x. inouts\<^sub>v' x = inouts1\<^sub>v x)" 
          by blast
        have c2: "(\<exists>ok\<^sub>v''' inouts\<^sub>v''''.
              (\<exists>inouts1\<^sub>v. \<forall>x. inouts\<^sub>v'''' x = inouts1\<^sub>v x) \<and>
              \<not> ok\<^sub>v \<and>
              (\<forall>x. inouts\<^sub>v x = inouts\<^sub>v x) \<and>
              more = more \<and>
              ok\<^sub>v' = (ok\<^sub>v' \<and> ok\<^sub>v''') \<and> 
              (\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v' x @ inouts\<^sub>v'''' x))"
          proof -
            obtain ok\<^sub>v''' and inouts\<^sub>v'''' where "ok\<^sub>v''' = ok\<^sub>v'" and "inouts\<^sub>v'''' = (\<lambda>x.[])"
              by auto
            have c3: "(\<exists>inouts1\<^sub>v. \<forall>x. [] = inouts1\<^sub>v x) \<and>
              \<not> ok\<^sub>v \<and>
              (\<forall>x. inouts\<^sub>v x = inouts\<^sub>v x) \<and>
              more = more \<and>
              ok\<^sub>v' = (ok\<^sub>v' \<and> ok\<^sub>v') \<and> 
              (\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v' x @ [])"
              using \<open>\<not> ok\<^sub>v\<close> by fastforce
            from c3 show ?thesis
              by metis
          qed
        from c1 and c2 show ?thesis
          by auto
      qed
    (* \<exists>x. P(x) *)
    then show ?thesis
      by metis
  qed
next
*)
  fix ok\<^sub>v :: "bool" and 
      inouts\<^sub>v and 
      more and 
      ok\<^sub>v':: "bool" and 
      inouts\<^sub>v'
  assume s1: " ok\<^sub>v'"
  assume s2: "\<forall>x. length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = 2 \<and> inouts\<^sub>v x = inouts\<^sub>v' x"
  show "\<exists>ok0\<^sub>v' inouts0\<^sub>v morea ok\<^sub>v'' inouts\<^sub>v''.
          (\<exists>inouts1\<^sub>v.
              (ok\<^sub>v \<longrightarrow> ok\<^sub>v'' \<and> (\<forall>x. length(inouts1\<^sub>v x) = Suc 0 \<and> hd (inouts\<^sub>v' x) = hd (inouts1\<^sub>v x))) \<and>
              (\<forall>x. inouts\<^sub>v'' x = inouts1\<^sub>v x)) \<and>
          (\<exists>ok\<^sub>v''' inouts\<^sub>v'''.
              (\<exists>inouts\<^sub>v.
                  (ok\<^sub>v \<longrightarrow> ok\<^sub>v''' \<and> (\<forall>x. length(inouts\<^sub>v x) = Suc 0 \<and> last (inouts\<^sub>v' x) = hd (inouts\<^sub>v x))) \<and>
                  (\<forall>x. inouts\<^sub>v''' x = inouts\<^sub>v x)) \<and>
              ok0\<^sub>v' = ok\<^sub>v \<and>
              (\<forall>x. inouts0\<^sub>v x = inouts\<^sub>v' x) \<and>
              morea = more \<and> ok\<^sub>v'' \<and> ok\<^sub>v''' \<and> (\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v'' x @ inouts\<^sub>v''' x))"
    proof -
      obtain ok0\<^sub>v' and inouts0\<^sub>v and morea and ok\<^sub>v'' and inouts\<^sub>v'' 
      where p: "ok0\<^sub>v' = ok\<^sub>v" and "inouts0\<^sub>v = inouts\<^sub>v'" and "morea = more" and "ok\<^sub>v''= True" and
        "inouts\<^sub>v'' = (\<lambda>x. [hd(inouts\<^sub>v' x)])"
        apply auto
      done
      have Px: "(\<exists>inouts1\<^sub>v.
              (ok\<^sub>v \<longrightarrow> True \<and> (\<forall>x. length(inouts1\<^sub>v x) = Suc 0 \<and> hd (inouts\<^sub>v' x) = hd (inouts1\<^sub>v x))) \<and>
              (\<forall>x. [hd(inouts\<^sub>v' x)] = inouts1\<^sub>v x)) \<and>
          (\<exists>ok\<^sub>v''' inouts\<^sub>v'''.
              (\<exists>inouts\<^sub>v.
                  (ok\<^sub>v \<longrightarrow> ok\<^sub>v''' \<and> (\<forall>x. length(inouts\<^sub>v x) = Suc 0 \<and> last (inouts\<^sub>v' x) = hd (inouts\<^sub>v x))) \<and>
                  (\<forall>x. inouts\<^sub>v''' x = inouts\<^sub>v x)) \<and>
              ok\<^sub>v = ok\<^sub>v \<and>
              (\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v' x) \<and>
              more = more \<and> True \<and> ok\<^sub>v''' \<and> (\<forall>x. inouts\<^sub>v' x = [hd(inouts\<^sub>v' x)] @ inouts\<^sub>v''' x))"
        proof -
          have c1: "(\<exists>inouts1\<^sub>v.
              (ok\<^sub>v \<longrightarrow> True \<and> (\<forall>x. length(inouts1\<^sub>v x) = Suc 0 \<and> hd (inouts\<^sub>v' x) = hd (inouts1\<^sub>v x))) \<and>
              (\<forall>x. [hd(inouts\<^sub>v' x)] = inouts1\<^sub>v x))"
            by (metis \<open>inouts\<^sub>v'' = (\<lambda>x. [hd (inouts\<^sub>v' x)])\<close> length_Cons list.sel(1) list.size(3))
          have c2: "(\<exists>ok\<^sub>v''' inouts\<^sub>v'''.
              (\<exists>inouts\<^sub>v.
                  (ok\<^sub>v \<longrightarrow> ok\<^sub>v''' \<and> (\<forall>x. length(inouts\<^sub>v x) = Suc 0 \<and> last (inouts\<^sub>v' x) = hd (inouts\<^sub>v x))) \<and>
                  (\<forall>x. inouts\<^sub>v''' x = inouts\<^sub>v x)) \<and>
              ok\<^sub>v = ok\<^sub>v \<and>
              (\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v' x) \<and>
              more = more \<and> True \<and> ok\<^sub>v''' \<and> (\<forall>x. inouts\<^sub>v' x = [hd(inouts\<^sub>v' x)] @ inouts\<^sub>v''' x))"
            proof -
              obtain ok\<^sub>v''' and inouts\<^sub>v''' where 
                "ok\<^sub>v''' = True" and "inouts\<^sub>v''' =  (\<lambda>x. [last(inouts\<^sub>v' x)])"
                by auto 
              have Px: "(\<exists>inouts\<^sub>v.
                  (ok\<^sub>v \<longrightarrow> True \<and> (\<forall>x. length(inouts\<^sub>v x) = Suc 0 \<and> last (inouts\<^sub>v' x) = hd (inouts\<^sub>v x))) \<and>
                  (\<forall>x. [last(inouts\<^sub>v' x)] = inouts\<^sub>v x)) \<and>
                ok\<^sub>v = ok\<^sub>v \<and>
                (\<forall>x. inouts\<^sub>v' x = inouts\<^sub>v' x) \<and>
                more = more \<and> True \<and> True \<and> (\<forall>x. inouts\<^sub>v' x = [hd(inouts\<^sub>v' x)] @ [last(inouts\<^sub>v' x)])"
                proof -
                  have c1: "(\<exists>inouts\<^sub>v.
                    (ok\<^sub>v \<longrightarrow> True \<and> (\<forall>x. length(inouts\<^sub>v x) = Suc 0 \<and> last (inouts\<^sub>v' x) = hd (inouts\<^sub>v x))) \<and>
                    (\<forall>x. [last(inouts\<^sub>v' x)] = inouts\<^sub>v x))"
                    by force
                  have c2: "(\<forall>x. inouts\<^sub>v' x = [hd(inouts\<^sub>v' x)] @ [last(inouts\<^sub>v' x)])"
                    using list_equal_size2 s2 by blast
                  from c1 and c2 show ?thesis
                    by auto
                qed
              then show ?thesis 
                by metis
            qed
          from c1 and c2 show ?thesis by auto
        qed
      then show ?thesis
        by metis
    qed
qed

paragraph {* Example *}
text {* For example, *}
definition IntegratorWOFeedback :: "(dummyT sim_state_scheme, dummyT sim_state_scheme) rel_des" where
"IntegratorWOFeedback = (true \<turnstile>\<^sub>r
        (\<^bold>\<forall> n::nat \<bullet> 
          (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 2) \<and> ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 2) \<and> 
          (head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a) + 
                (if n = 0 then 0 else head\<^sub>u(tail\<^sub>u($inouts (\<guillemotleft>n-1\<guillemotright>)\<^sub>a)))) \<and>
          head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u(tail\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)))
        ))"

definition PreFD1 :: "(nat \<Rightarrow> real) \<Rightarrow> (dummyT sim_state_scheme, dummyT sim_state_scheme) rel_des" where
"PreFD1 x = (true \<turnstile>\<^sub>r
        (\<^bold>\<forall> n::nat \<bullet> 
          (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 2) \<and> 
          (head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) \<and> 
          (head\<^sub>u(tail\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u (\<guillemotleft>x n\<guillemotright>))) ))"

definition PostFD1 :: "(nat \<Rightarrow> real) \<Rightarrow> (dummyT sim_state_scheme, dummyT sim_state_scheme) rel_des" where
"PostFD1 x = (true \<turnstile>\<^sub>r
        (\<^bold>\<forall> n::nat \<bullet> 
          (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 2) \<and> ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> 
          (head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) \<and> 
          (head\<^sub>u(tail\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u (\<guillemotleft>x n\<guillemotright>))) ))"

definition Integrator :: "(dummyT sim_state_scheme, dummyT sim_state_scheme) rel_des" where 
"Integrator = (true \<turnstile>\<^sub>r
        (\<^bold>\<forall> n::nat \<bullet> 
          (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> 
          (head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a) + 
                (if n = 0 then 0 else head\<^sub>u($inouts\<acute> (\<guillemotleft>n-1\<guillemotright>)\<^sub>a))))
        ))"

definition IntegratorWCFeedback :: "(dummyT sim_state_scheme, dummyT sim_state_scheme) rel_des" where
"IntegratorWCFeedback = (\<^bold>\<exists> (x) \<bullet> ((PreFD1 x) ;; IntegratorWOFeedback ;; (PostFD1 x)))"

(*
lemma "IntegratorWCFeedback = Integrator"
apply (simp add: IntegratorWCFeedback_def Integrator_def)
apply (simp add: PreFD1_def PostFD1_def IntegratorWOFeedback_def)
apply (rel_auto)
apply (metis not_gr0)
-- {* Goal 2: *}
proof - (* 2 *)
  fix inouts\<^sub>v :: "nat \<Rightarrow> real list" and inouts\<^sub>v':: "nat \<Rightarrow> real list" and ok\<^sub>v and ok\<^sub>v'
  assume s1: "ok\<^sub>v" and "ok\<^sub>v'"
  assume s2: "\<forall>x. (x = 0 \<longrightarrow> length(inouts\<^sub>v 0) = Suc 0 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> 
                  hd (inouts\<^sub>v' 0) = hd (inouts\<^sub>v 0)) \<and>
           (0 < x \<longrightarrow>  length(inouts\<^sub>v x) = Suc 0 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> 
                  hd (inouts\<^sub>v' x) = hd (inouts\<^sub>v x) + hd (inouts\<^sub>v' (x - Suc 0)))"
  show "\<exists>x inouts\<^sub>v''.
          (\<forall>xa. length(inouts\<^sub>v xa) = Suc 0 \<and> length(inouts\<^sub>v'' xa) = 2 \<and> 
              hd (inouts\<^sub>v'' xa) = hd (inouts\<^sub>v xa) \<and> hd (tl (inouts\<^sub>v'' xa)) = x xa) \<and>
          (\<exists>inouts\<^sub>v.
              (\<forall>x. (x = 0 \<longrightarrow> length(inouts\<^sub>v'' 0) = 2 \<and> length(inouts\<^sub>v 0) = 2 \<and> 
                        hd (inouts\<^sub>v 0) = hd (inouts\<^sub>v'' 0) \<and> hd (inouts\<^sub>v 0) = hd (tl (inouts\<^sub>v 0))) \<and>
                   (0 < x \<longrightarrow> length(inouts\<^sub>v'' x) = 2 \<and> length(inouts\<^sub>v x) = 2 \<and>
                      hd (inouts\<^sub>v x) = hd (inouts\<^sub>v'' x) + hd (tl (inouts\<^sub>v'' (x - Suc 0))) \<and>
                      hd (inouts\<^sub>v x) = hd (tl (inouts\<^sub>v x)))) \<and>
              (\<forall>xa. length(inouts\<^sub>v xa) = 2 \<and> length(inouts\<^sub>v' xa) = Suc 0 \<and> 
                  hd (inouts\<^sub>v' xa) = hd (inouts\<^sub>v xa) \<and> hd (tl (inouts\<^sub>v xa)) = x xa))"
  -- {* Goal 2.1: unroll forall*}
  proof - (* 2.1 *)
    let ?x = "(\<lambda>n. (if n = 0 then hd (inouts\<^sub>v n) else hd (inouts\<^sub>v n) + hd (inouts\<^sub>v' (n - Suc 0))))"
    obtain x and inouts\<^sub>v'' where 
      p: "x = ?x"  and "inouts\<^sub>v'' = (\<lambda>n.[hd (inouts\<^sub>v n), ?x n])"
        by auto
    (* P(x) *)
    let ?P = "\<lambda>u v . (\<forall>xa. length(inouts\<^sub>v xa) = Suc 0 \<and> length(u xa) = 2 \<and> 
            hd (u xa) = hd (inouts\<^sub>v xa) \<and> hd (tl (u xa)) = v xa) \<and>
        (\<exists>inouts\<^sub>v.
            (\<forall>x. (x = 0 \<longrightarrow> length(u 0) = 2 \<and> length(inouts\<^sub>v 0) = 2 \<and> 
                      hd (inouts\<^sub>v 0) = hd (u 0) \<and> hd (inouts\<^sub>v 0) = hd (tl (inouts\<^sub>v 0))) \<and>
                 (0 < x \<longrightarrow> length(u x) = 2 \<and> length(inouts\<^sub>v x) = 2 \<and>
                    hd (inouts\<^sub>v x) = hd (u x) + hd (tl (u (x - Suc 0))) \<and>
                    hd (inouts\<^sub>v x) = hd (tl (inouts\<^sub>v x)))) \<and>
            (\<forall>xa. length(inouts\<^sub>v xa) = 2 \<and> length(inouts\<^sub>v' xa) = Suc 0 \<and> 
                hd (inouts\<^sub>v' xa) = hd (inouts\<^sub>v xa) \<and> hd (tl (inouts\<^sub>v xa)) = v xa))"
    -- {* Goal 2.1.1 : unroll exists *}
    have Px: "?P (\<lambda>n.[hd (inouts\<^sub>v n), ?x n]) (?x)"
      proof - (* 2.1.1 *)
        have 0: "\<forall>xa. length(inouts\<^sub>v xa) = Suc 0"
          using neq0_conv s2 by blast
        -- {* Goal 2.1.1.1 : 1st conjunction *}
        then have 1: "(\<forall>xa. length(inouts\<^sub>v xa) = Suc 0 \<and>
          length([hd (inouts\<^sub>v xa), ?x xa]) = 2 \<and> hd [hd (inouts\<^sub>v xa), ?x xa] =
          hd (inouts\<^sub>v xa) \<and>
          hd (tl [hd (inouts\<^sub>v xa), ?x xa]) = ?x xa)"
          by simp
        -- {* Goal 2.1.1.2 : 2nd conjunction *}
        let ?P2 = "(\<lambda>inouts\<^sub>v'' :: nat\<Rightarrow>real list.
          (\<forall>x. (x = 0 \<longrightarrow>
            length([hd (inouts\<^sub>v 0), ?x 0]) = 2 \<and>
            length(inouts\<^sub>v'' 0) = 2 \<and>
            hd (inouts\<^sub>v'' 0) = hd [hd (inouts\<^sub>v 0), ?x 0] \<and>
            hd (inouts\<^sub>v'' 0) = hd (tl (inouts\<^sub>v'' 0))) \<and>
           (0 < x \<longrightarrow>
            length([hd (inouts\<^sub>v x), ?x x]) = 2 \<and>
            length(inouts\<^sub>v'' x) = 2 \<and>
            hd (inouts\<^sub>v'' x) = hd [hd (inouts\<^sub>v x), ?x x] +
            hd (tl [hd (inouts\<^sub>v (x - Suc 0)),
                    if x - Suc 0 = 0 then hd (inouts\<^sub>v (x - Suc 0))
                    else hd (inouts\<^sub>v (x - Suc 0)) + hd (inouts\<^sub>v' (x - Suc 0 - Suc 0))]) \<and>
            hd (inouts\<^sub>v'' x) = hd (tl (inouts\<^sub>v'' x)))) \<and>
          (\<forall>xa. length(inouts\<^sub>v'' xa) = 2 \<and>
            length(inouts\<^sub>v' xa) = Suc 0 \<and>
            hd (inouts\<^sub>v' xa) = hd (inouts\<^sub>v'' xa) \<and>
            hd (tl (inouts\<^sub>v'' xa)) =
            (if xa = 0 then hd (inouts\<^sub>v xa) else hd (inouts\<^sub>v xa) + hd (inouts\<^sub>v' (xa - Suc 0)))))"
        -- {* Goal 2.1.1.2 : 2nd conjunction *}
        have 2: "(\<exists>inouts\<^sub>v''. (?P2 inouts\<^sub>v''))"
          proof - (* 2.1.1 *)
            -- {* Goal 2.1.1.2.1 : unroll exists *}
            let ?t = "\<lambda>n.(hd (inouts\<^sub>v n) + (
                  if n = 0 then 0 else 
                    if n = 1 then hd (inouts\<^sub>v (n-1)) else 
                      hd (inouts\<^sub>v (n-1)) + hd (inouts\<^sub>v' (n - 2))))"
            obtain inouts\<^sub>v'' where p: "inouts\<^sub>v''= (\<lambda>n.[?t n,?t n])"
              by auto
            have P2x: "?P2 (\<lambda>n.[?t n,?t n])"
              proof - (* 2.1.1.1 *)
                -- {* Goal 2.1.1.2.1.1 : 1st conjunction *}
                have 11: "\<forall>x. (x = 0 \<longrightarrow>
                  length([hd (inouts\<^sub>v 0), ?x 0]) = 2 \<and>
                  length([?t 0, ?t 0]) = 2 \<and>
                  hd [?t 0, ?t 0] = hd [hd (inouts\<^sub>v 0), ?x 0] \<and>
                  hd [?t 0, ?t 0] = hd (tl [?t 0, ?t 0]))"
                  by simp
                -- {* Goal 2.1.1.2.1.2 : 2st conjunction *}
                have 12: "(\<forall>x.(0 < x \<longrightarrow>
                  length([hd (inouts\<^sub>v x), ?x 0]) = 2 \<and>
                  length([?t x, ?t x]) = 2 \<and>
                  hd [?t x, ?t x] = hd [hd (inouts\<^sub>v x), ?x x] +
                      hd (tl [hd (inouts\<^sub>v (x - Suc 0)),
                          if x - Suc 0 = 0 then hd (inouts\<^sub>v (x - Suc 0))
                          else hd (inouts\<^sub>v (x - Suc 0)) + hd (inouts\<^sub>v' (x - Suc 0 - Suc 0))]) \<and>
                  hd [?t x, ?t x] = hd (tl [?t x, ?t x])))"
                  by (smt Suc_1 Suc_diff_eq_diff_pred diff_Suc_1 length_Cons less_imp_Suc_add list.sel(1) list.sel(3) list.size(3) neq0_conv numeral_1_eq_Suc_0 numeral_One pos2)
                -- {* Goal 2.1.1.2.1.3 : 3rd conjunction *}
                have 13: "(\<forall>xa. length([?t xa, ?t xa]) =  2 \<and>
                    length(inouts\<^sub>v' xa) = Suc 0 \<and>
                    hd (inouts\<^sub>v' xa) = hd [?t xa, ?t xa] \<and>
                    hd (tl [?t xa, ?t xa]) = (?x xa))"
                  using "12" s2 by auto
                show ?thesis using 11 12 13
                  by simp
              qed -- {* Goal 2.1.1.2.1 : 1st conjunction *} (* 2.1.1.1 *)
            show ?thesis using P2x 
              sorry (* proof found but slow *)
          qed -- {* Goal 2.1.1.2 *} (* 2.1.1 *)
        then show ?thesis using 1 2
          by blast
      qed  -- {* Goal 2.1.1 *} (* 2.1 *)
    then show ?thesis using Px 
      by (metis \<open>\<And>thesis. (\<And>x inouts\<^sub>v''. \<lbrakk>x = (\<lambda>n. if n = 0 then hd (inouts\<^sub>v n) else hd (inouts\<^sub>v n) + hd (inouts\<^sub>v' (n - Suc 0))); inouts\<^sub>v'' = (\<lambda>n. [hd (inouts\<^sub>v n), if n = 0 then hd (inouts\<^sub>v n) else hd (inouts\<^sub>v n) + hd (inouts\<^sub>v' (n - Suc 0))])\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
  qed (* 2 *)
qed
*)

(*
lemma "(inps IntegratorWOFeedback) = 2"
proof -
  have 1: "IntegratorWOFeedback is HDim 2"
    apply (simp add: IntegratorWOFeedback_def Healthy_def sim_blocks)
    apply (ndes_simp) 
    sorry
  then show ?thesis
    apply (simp add: inps_dim)
  done
qed
*)
(*
lemma "IntegratorWOFeedback f\<^sub>D [(1,1)] = Integrator"
apply (simp add: sim_blocks IntegratorWOFeedback_def Integrator_def)
apply (rel_auto)
  apply blast
  apply blast
  apply blast
(*  apply blast
  apply blast
  apply blast *)
sorry

lemma "IntegratorWCFeedback = IntegratorWOFeedback f\<^sub>D [(1,1)]"
apply (simp add: sim_blocks IntegratorWCFeedback_def PreFD1_def PostFD1_def IntegratorWOFeedback_def)
apply (rel_auto)
  apply blast
  apply blast
  apply blast
(*  apply blast
  apply blast
  apply blast *)
sorry
*)

subsection {* Examples *}

subsubsection {* PID Integrator *}
fun listsum :: "real list \<Rightarrow> real" where
  "listsum [] = 0" |
  "listsum (x # xs) = x + listsum xs" 

term "(map nat [0..n])"
term "head\<^sub>u($inouts (\<guillemotleft>x\<guillemotright>)\<^sub>a)"
term "(\<lambda>x \<bullet> head\<^sub>u($inouts (\<guillemotleft>x\<guillemotright>)\<^sub>a))"
term "(\<guillemotleft>map\<guillemotright> (\<lambda>x \<bullet> head\<^sub>u($inouts (\<guillemotleft>x\<guillemotright>)\<^sub>a))\<^sub>a (\<guillemotleft>(map nat [0..n])\<guillemotright>)\<^sub>a)"
term "(\<guillemotleft>list_sum\<guillemotright> (\<guillemotleft>map\<guillemotright> (\<lambda>x \<bullet> head\<^sub>u($inouts (\<guillemotleft>x\<guillemotright>)\<^sub>a))\<^sub>a (\<guillemotleft>(map nat [0..n])\<guillemotright>)\<^sub>a)\<^sub>a) + 0"
term "head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)"
term "head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts (\<guillemotleft>x\<guillemotright>)\<^sub>a)"
(*
term "(head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u 
  ((\<guillemotleft>list_sum\<guillemotright> (\<guillemotleft>map\<guillemotright> (\<lambda>x \<bullet> head\<^sub>u($inouts (\<guillemotleft>x\<guillemotright>)\<^sub>a))\<^sub>a (\<guillemotleft>(map nat [0..n])\<guillemotright>)\<^sub>a)\<^sub>a) + 0))"
*)

lemma sum_1:
  fixes n :: "nat" and x :: "nat \<Rightarrow> real" and y :: "nat \<Rightarrow> real"
  assumes "\<forall>n. (x(n) = y(n) + (if (n = 0) then 1 else x(n-1)))"
  shows "(x(n) = list_sum (map (\<lambda>x. y(x)) (map nat [0..n])) + 1)"
proof (induction n)
  case 0
  then show ?case 
    proof -
      from assms have 0: "x(0) = y(0) + 1"
        by simp
      have 1: "list_sum (map (\<lambda>x. y(x)) (map nat [0..0])) = y(0)"
        by (simp add: upto.simps)
      from 0 1 show ?thesis 
        by auto
    qed
next
  case (Suc n)
  then show ?case 
    proof -
      have 00: "(map y (map nat [0..int (Suc n)])) = (map y (map nat [0..int n])) @ [y(Suc n)]"
        by (smt list.simps(8) list.simps(9) map_append nat_int of_nat_0_le_iff of_nat_Suc upto_rec2)
      then have 01: "(foldr op + (map y (map nat [0..int (Suc n)])) 0) = 
                     (foldr op + (map y (map nat [0..int (n)])) 0) + y(Suc n)"
        sorry
      from assms have 0: "x (Suc n) = y(Suc n) + x(n)"
        by simp
      then have 1: "... = y(Suc n) + (foldr op + (map y (map nat [0..int n])) 0 + 1)"
        by (simp add: Suc.IH)
      then have 2: "... = (foldr op + (map y (map nat [0..int (Suc n)])) 0 + 1)"
        using "01" by auto
      show ?thesis
       using "0" "2" Suc.IH by linarith
    qed
qed

(*
lemma pid_int_l1:
  shows "
  (true \<turnstile>\<^sub>r
        (\<^bold>\<forall> n::nat \<bullet> 
          (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> 
          (head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a) + 
                (if n = 0 then 0 else head\<^sub>u($inouts\<acute> (\<guillemotleft>n-1\<guillemotright>)\<^sub>a))))
        )
  )
   = 
  (true \<turnstile>\<^sub>r
        (\<^bold>\<forall> n::nat \<bullet> 
          (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> 
          (head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u ((\<guillemotleft>list_sum\<guillemotright> (\<guillemotleft>map\<guillemotright> (\<lambda>x \<bullet> head\<^sub>u($inouts (\<guillemotleft>x\<guillemotright>)\<^sub>a))\<^sub>a (\<guillemotleft>(map nat [0..n])\<guillemotright>)\<^sub>a)\<^sub>a) + 0)))
        )
      )"
sorry

(* (head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u ((\<guillemotleft>sum_list\<guillemotright> (\<guillemotleft>map\<guillemotright> (\<lambda>x \<bullet> head\<^sub>u($inouts (\<guillemotleft>x\<guillemotright>)\<^sub>a))\<^sub>a (\<guillemotleft>[0..n]\<guillemotright>)\<^sub>a)) + 0) *)

lemma pid_int:
  shows "((Id \<parallel>\<^sub>D (UnitDelay 0)) ;; Sum) =
      (true \<turnstile>\<^sub>r
        (\<^bold>\<forall> n::nat \<bullet> 
          (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 2) \<and> ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> 
          (head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a) + 
                (if n = 0 then 0 else (\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>n-1\<guillemotright>)\<^sub>a)\<^sub>a (1)\<^sub>a))))
        )
      )"
sorry

term " (\<lambda>x. head\<^sub>u($inouts (\<guillemotleft>x\<guillemotright>)\<^sub>a))"
term "map (\<lambda>x. head\<^sub>u($inouts (\<guillemotleft>x\<guillemotright>)\<^sub>a)) (map nat [0..n])"

lemma pid_int_feed:
  shows "(true \<turnstile>\<^sub>r
        (\<^bold>\<forall> n::nat \<bullet> 
          (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> 
          (head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a) + 
                (if n = 0 then 1 else head\<^sub>u($inouts\<acute> (\<guillemotleft>n-1\<guillemotright>)\<^sub>a))))
        )
      ) = (true \<turnstile>\<^sub>r
        (\<^bold>\<forall> n::nat \<bullet> 
          (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> 
          (head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u (\<guillemotleft>list_sum\<guillemotright> (map (\<lambda>x. head\<^sub>u($inouts (\<guillemotleft>x\<guillemotright>)\<^sub>a)) (map (nat) ([0..n])))\<^sub>a) + 1))
        )
      )"
apply (rel_auto)
*)


end