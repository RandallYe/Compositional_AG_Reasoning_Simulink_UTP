section {* Post Landing Finalize \label{sec:post_landing} *}

text {* This is a case study of a subsystem named post landing finalize that is used in aircraft 
cabin pressure control application. It is from \href{https://www.honeywell.com/}{Honeywell} through 
\href{http://www.drisq.com/}{D-risQ}. This case is published in \cite{Bhatt2016} and the diagram of 
this subsystem is shown in Figure 2 of the paper. *}

theory post_landing_finalize_1 
  imports 
    (* "~~/src/HOL/Decision_Procs/Approximation" *)
    simu_contract_real
    simu_contract_real_laws
begin

recall_syntax 

sledgehammer_params[
  timeout = 200,
  verbose = false,
  strict = true
]

subsection {* Subsystem: @{text "variableTimer"} \label{ssec:plf_variableTimer} *}
text {* This subsystem has a rate parameter which is equal to 10. *}
abbreviation "Rate \<equiv> 10"

text {* This subsystem is composed of two small parts: @{text "variableTimer1"} and 
@{text "variableTimer2"}.
*}
(* 
 inputs: (5\<longrightarrow>14), (13\<longrightarrow>14), (in1 \<longrightarrow> 5)
 outputs: (5 \<longrightarrow> 14), (5 \<longrightarrow> varConfirm_1)
*)
abbreviation "variableTimer1 \<equiv> 
  ((((Min2 ;; UnitDelay 0) \<parallel>\<^sub>B (Const 1)) ;; Sum2) \<parallel>\<^sub>B Id \<parallel>\<^sub>B (Const 0)) ;; (Switch1 0.5) ;; Split2"

text {* @{text "variableTimer1"} is simplified by @{text "variableTimer1_simp"} to a simple design. *}
lemma variableTimer1_simp:
  "variableTimer1 = (FBlock (\<lambda>x n. True) (3) 2 (\<lambda>x n. [if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
          if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0]))"
  proof -
    (* (Min2 ;; UnitDelay 0) *)
    have f1: "(Min2 ;; UnitDelay 0) = (FBlock (\<lambda>x n. True) (2) (1) ((f_UnitDelay 0) o f_Min2))"
      using SimBlock_Min2 SimBlock_UnitDelay apply (simp add: FBlock_parallel_comp f_sim_blocks)
      by (simp add: FBlock_seq_comp)
    then have f1_0: "... = (FBlock (\<lambda>x n. True) (2) (1) 
        (\<lambda>x n. [if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))]))"
    proof -
      have "FBlock (\<lambda>f n. True) 2 1 (f_UnitDelay 0 \<circ> f_Min2) = FBlock (\<lambda>f n. True) 2 1 
            (\<lambda>f n. [if n = 0 then 0 else min (hd (f (n - 1))) (hd (tl (f (n - 1))))]) \<or> 
            (\<forall>f n. (f_UnitDelay 0 \<circ> f_Min2) f n = [if n = 0 then 0 else 
                    min (hd (f (n - 1))) (hd (tl (f (n - 1))))])"
        by (simp add: f_Min2_def f_UnitDelay_def)
      then show ?thesis
        by meson
    qed
    have simblock_f1: "SimBlock 2 1 (FBlock (\<lambda>x n. True) (2) (1) 
        (\<lambda>x n. [if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))]))"
      by (metis (no_types, lifting) Min2_def SimBlock_Min2 SimBlock_FBlock_seq_comp 
          SimBlock_UnitDelay UnitDelay_def f1 f1_0)
    (* ((Min2 ;; UnitDelay 0) \<parallel>\<^sub>B (Const 1)) *)
    have 1: "((\<lambda>x n. [if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))]) \<circ> 
                (\<lambda>xx nn. take 2 (xx nn)))
      = (\<lambda>x n. [if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))])"
    proof -
      have "\<forall>x n. (((\<lambda>x n. [if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))]) \<circ> 
                (\<lambda>xx nn. take 2 (xx nn))) x n 
          = (\<lambda>x n. [if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))]) x n)"
      apply (rule allI)+
      proof -
        fix x :: "'c \<Rightarrow> 'd list" and n :: 'c
        have f1: "\<forall>ds. ds = [] \<or> (hd ds::'d) = ds!(0::nat)"
          using hd_conv_nth by blast
        have f2: "\<not> x (n - 1) = [] \<longrightarrow> \<not> take 2 (x (n - 1)) = []"
          by simp
        have f3: "take (Suc 0) (tl (x (n - 1))) = tl (take (Suc (Suc 0)) (x (n - 1)))"
          by (simp add: tl_take)
        have f4: "take 2 (x (n - 1)) = take (Suc (Suc 0)) (x (n - 1))"
          using numeral_2_eq_2 by presburger
        have f5: "hd (tl (x (n - 1))) = tl (x (n - 1))!(0::nat) \<and> 
                  hd (tl (take 2 (x (n - 1)))) = tl (take 2 (x (n - 1)))!(0::nat) \<and> 
                  \<not> x (n - 1) = [] \<longrightarrow> min (hd (take 2 (x (n - 1)))) 
                  (hd (tl (take 2 (x (n - 1))))) = min (hd (x (n - 1))) (hd (tl (x (n - 1))))"
          using f3 f2 f1 by (metis One_nat_def less_numeral_extra(1) nth_take numeral_2_eq_2 pos2)
        have f6: "\<not> tl (take 2 (x (n - 1))) = [] \<longrightarrow> \<not> Suc 0 = 0 \<and> \<not> tl (x (n - 1)) = []"
          using f4 f3 by fastforce
        have f7: "\<not> Suc 0 = 0"
          by blast
        { assume "\<not> ((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))]"
        { assume "\<not> (if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))) = min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))"
          moreover
          { assume "\<not> min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1))))) = min (hd (x (n - 1))) (hd (tl (x (n - 1))))"
          moreover
            { assume "\<not> hd (take 2 (x (n - 1))) = hd (x (n - 1))"
              { assume "\<not> x (n - 1) = []"
                moreover
          { assume "tl (x (n - 1)) = [] \<and> hd (x (n - 1)) = x (n - 1)!(0::nat) \<and> hd (take 2 (x (n - 1))) = take 2 (x (n - 1))!(0::nat)"
            moreover
                  { assume "(tl (x (n - 1)) = [] \<and> hd (x (n - 1)) = x (n - 1)!(0::nat) \<and> hd (take 2 (x (n - 1))) = take 2 (x (n - 1))!(0::nat)) \<and> \<not> ((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))]"
                    moreover
                    { assume "(tl (x (n - 1)) = [] \<and> hd (x (n - 1)) = x (n - 1)!(0::nat) \<and> hd (take 2 (x (n - 1))) = take 2 (x (n - 1))!(0::nat)) \<and> \<not> (if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))) = min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))"
        then have "tl (take 2 (x (n - 1))) = [] \<longrightarrow> n = 0"
                        by (metis (no_types) nth_take pos2) }
                    ultimately have "((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))] \<and> tl (take 2 (x (n - 1))) = [] \<longrightarrow> n = 0"
                      by fastforce }
                  ultimately have "((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))] \<and> tl (take 2 (x (n - 1))) = [] \<longrightarrow> ((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))] \<or> n = 0"
                    by blast }
                moreover
                { assume "\<not> tl (x (n - 1)) = []"
                  then have "\<not> tl (take 2 (x (n - 1))) = []"
                    using f7 f4 f3 by (metis (no_types) take_eq_Nil) }
                ultimately have "((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))] \<and> tl (take 2 (x (n - 1))) = [] \<longrightarrow> ((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))] \<or> n = 0"
                  using f2 f1 by blast }
              then have "((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))] \<and> tl (take 2 (x (n - 1))) = [] \<longrightarrow> ((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))] \<or> n = 0"
                by fastforce }
            moreover
            { assume "\<not> tl (take 2 (x (n - 1))) = []"
              moreover
              { assume "\<not> tl (take 2 (x (n - 1))) = [] \<and> \<not> ((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))]"
                moreover
                { assume "\<not> tl (take 2 (x (n - 1))) = [] \<and> \<not> (if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))) = min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))"
                  moreover
                  { assume "\<not> tl (take 2 (x (n - 1))) = [] \<and> \<not> min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1))))) = min (hd (x (n - 1))) (hd (tl (x (n - 1))))"
                    then have "\<not> tl (take 2 (x (n - 1))) = [] \<and> \<not> x (n - 1) = []"
                      by (metis take_eq_Nil)
                    moreover
                    { assume "(hd (tl (x (n - 1))) = tl (x (n - 1))!(0::nat) \<and> hd (tl (take 2 (x (n - 1)))) = tl (take 2 (x (n - 1)))!(0::nat) \<and> \<not> x (n - 1) = []) \<and> \<not> ((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))]"
                      then have "((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))] \<longrightarrow> (hd (tl (x (n - 1))) = tl (x (n - 1))!(0::nat) \<and> hd (tl (take 2 (x (n - 1)))) = tl (take 2 (x (n - 1)))!(0::nat) \<and> \<not> x (n - 1) = []) \<and> \<not> (if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))) = min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))"
                        by fastforce
                      then have "((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))] \<longrightarrow> n = 0"
                        using f5 by (metis (no_types)) }
                      ultimately have "((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))] \<longrightarrow> ((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))] \<or> n = 0"
                        using f6 f1 by blast }
                      ultimately have "((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))] \<longrightarrow> ((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))] \<or> n = 0"
                        by fastforce }
                      ultimately have "((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))] \<longrightarrow> ((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))] \<or> n = 0"
                        by force }
                  ultimately have "((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))] \<longrightarrow> ((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))] \<or> n = 0"
                    by blast }
                ultimately have "((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))] \<longrightarrow> ((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))] \<or> n = 0"
                  using f3 numeral_2_eq_2 by force }
              ultimately have "((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))] \<longrightarrow> ((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))] \<or> n = 0"
                  by presburger }
        moreover
        { assume "\<not> ((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))]"
          then have "\<not> [if n = 0 then 0 else min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))] = [min (hd (take 2 (x (n - 1)))) (hd (tl (take 2 (x (n - 1)))))]"
            by simp
          then have "n = 0"
            by presburger }
        ultimately have "((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))]"
          by fastforce }
        then show "((\<lambda>f c. [if c = 0 then 0 else min (hd (f (c - 1))) (hd (tl (f (c - 1))))]) \<circ> (\<lambda>f c. take 2 (f c))) x n = [if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))]"
          by blast
      qed
      then show ?thesis
      by blast
    qed
    have f2: "((Min2 ;; UnitDelay 0) \<parallel>\<^sub>B (Const 1)) = 
        (FBlock (\<lambda>x n. True) (2) (1) 
        (\<lambda>x n. [if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))]))  \<parallel>\<^sub>B (Const 1) "
      using f1 f1_0 by auto
    then have f2_0: "... = FBlock (\<lambda>x n. True) (2) (2) 
        (\<lambda>x n. ((((\<lambda>x n. [if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))]) \<circ> 
                  (\<lambda>xx nn. take 2 (xx nn))) x n) 
             @ (((f_Const 1) \<circ> (\<lambda>xx nn. drop 2 (xx nn)))) x n))"
      using SimBlock_Const simblock_f1 apply (simp add: FBlock_parallel_comp f_sim_blocks)
      by (simp add: numeral_2_eq_2)
    then have f2_1: "... = FBlock (\<lambda>x n. True) (2) (2) 
        (\<lambda>x n. [if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1))))), 1])"
      using 1 f_Const_def by (simp add: "1")
    have simblock_f2: "SimBlock 2 2 (FBlock (\<lambda>x n. True) (2) (2) 
        (\<lambda>x n. [if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1))))), 1]))"
      by (metis (no_types, lifting) Const_def SimBlock_Const SimBlock_FBlock_parallel_comp 
          Suc_1 Suc_eq_plus1 add_2_eq_Suc f2_0 f2_1 numeral_2_eq_2 simblock_f1)
    (* (((Min2 ;; UnitDelay 0) \<parallel>\<^sub>B (Const 1)) ;; Sum2) *)
    have f3: "(((Min2 ;; UnitDelay 0) \<parallel>\<^sub>B (Const 1)) ;; Sum2) = 
      (FBlock (\<lambda>x n. True) (2) (2) 
        (\<lambda>x n. [if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1))))), 1])) ;; Sum2"
      using f2 f2_0 f2_1 by auto
    have f3_0: "... = (FBlock (\<lambda>x n. True) (2) (1) 
        (f_Sum2 o (\<lambda>x n. [(if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))), 1])))"
      using SimBlock_Sum2 simblock_f2 by (simp add: FBlock_seq_comp f_sim_blocks)
    have f3_1: "... = (FBlock (\<lambda>x n. True) (2) (1) 
        (\<lambda>x n. [(if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1]))"
      proof -
        have "\<forall>x n. ((f_Sum2 o (\<lambda>x n. [(if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))), 1])) x n)
            = ((\<lambda>x n. [(if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1]) x n)"
          by (simp add: f_Sum2_def)
        then show ?thesis
          by presburger
      qed
    have simblock_f3: "SimBlock 2 1 (FBlock (\<lambda>x n. True) (2) (1) 
        (\<lambda>x n. [(if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1]))"
      by (metis (no_types, lifting) SimBlock_FBlock_seq_comp SimBlock_Sum2 Sum2_def f3_0 f3_1 simblock_f2)
    (* Id \<parallel>\<^sub>B (Const 0) *)
    have f4: "(Id \<parallel>\<^sub>B (Const 0)) = (FBlock (\<lambda>x n. True) (1) (2) 
        (\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ (((f_Const 0) \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)))"
      using SimBlock_Const SimBlock_Id apply (simp add: FBlock_parallel_comp f_sim_blocks)
      by (simp add: numeral_2_eq_2)
    then have f4_0: "... = FBlock (\<lambda>x n. True) 1 2 (\<lambda>x n. [hd(x n), 0])"
      proof -
        have "\<forall>x n. ((\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                  (((f_Const 0) \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)) x n) 
          = ((\<lambda>x n. [hd(x n), 0]) x n)"
          by (smt append.left_neutral append_Cons append_take_drop_id comp_apply f_Const_def 
            f_Id_def hd_append2 take_eq_Nil zero_neq_one)
        then show ?thesis
          by presburger
      qed
    have simblock_f4: "SimBlock (Suc 0) 2 (FBlock (\<lambda>x n. True) (Suc 0) 2 (\<lambda>x n. [hd(x n), 0]))"
      using SimBlock_Const SimBlock_Id SimBlock_FBlock_seq_comp
      by (metis (no_types, lifting) Const_def Id_def One_nat_def SimBlock_FBlock_parallel_comp 
          Suc_eq_plus1_left f4 f4_0 nat_1_add_1)
    (* ((((Min2 ;; UnitDelay 0) \<parallel>\<^sub>B (Const 1)) ;; Sum2) \<parallel>\<^sub>B Id) *)
    have f5: "((((Min2 ;; UnitDelay 0) \<parallel>\<^sub>B (Const 1)) ;; Sum2) \<parallel>\<^sub>B Id) = 
      (FBlock (\<lambda>x n. True) (2) (1) 
        (\<lambda>x n. [(if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1])) \<parallel>\<^sub>B Id"
      using f3 f3_0 f3_1 by auto 
    then have f5_0: "... = 
      (FBlock (\<lambda>x n. True) (3) (2)
        (\<lambda>x n. ((((\<lambda>x n. [(if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1])
                   \<circ> (\<lambda>xx nn. take 2 (xx nn))) x n) 
             @ ((f_Id \<circ> (\<lambda>xx nn. drop 2 (xx nn)))) x n)))"
      using simblock_f3 SimBlock_Id apply (simp add: FBlock_parallel_comp f_sim_blocks)
      by (simp add: numeral_2_eq_2)
    then have f5_1: "... = 
      (FBlock (\<lambda>x n. True) (3) (2)
        (\<lambda>x n. [(if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1, (x n)!2]))"
      proof -
        have 11: "\<forall>inouts\<^sub>v x. (min (hd (take 2 (inouts\<^sub>v (x - Suc 0)))) (hd (tl (take 2 (inouts\<^sub>v (x - Suc 0))))) + 1)
              = min (hd (inouts\<^sub>v (x - Suc 0))) (hd (tl (inouts\<^sub>v (x - Suc 0)))) + 1"
          by (smt Suc_1 append_take_drop_id diff_Suc_1 hd_append2 take_eq_Nil tl_take zero_neq_one zero_not_eq_two)
        have 12: "\<forall>inouts\<^sub>v x. (length(inouts\<^sub>v x) = 3 \<longrightarrow> 
            (f_Id (\<lambda>nn. drop 2 (inouts\<^sub>v nn)) x) = [inouts\<^sub>v x!(2)])"
          by (simp add: f_Id_def hd_drop_conv_nth)
        have 2: "\<forall>inouts\<^sub>v x. (length(inouts\<^sub>v x) = 3 \<longrightarrow> 
            (((min (hd (take 2 (inouts\<^sub>v (x - Suc 0)))) (hd (tl (take 2 (inouts\<^sub>v (x - Suc 0))))) + 1) #
            f_Id (\<lambda>nn. drop 2 (inouts\<^sub>v nn)) x)
          = [min (hd (inouts\<^sub>v (x - Suc 0))) (hd (tl (inouts\<^sub>v (x - Suc 0)))) + 1, inouts\<^sub>v x!(2)]))"
          using "11" "12" by blast
        show ?thesis
          apply (simp add: FBlock_def)
          apply (rel_auto)
          apply (metis (no_types, lifting) One_nat_def Suc_1 f_Id_def hd_drop_conv_nth lessI numeral_3_eq_3)
          using 11 12 2
          apply metis
          apply (simp add: "12")
          apply (simp add: "11" "12")
          by (simp add: f_Id_def)
      qed
    have simblock_f5: "SimBlock 3 2 (FBlock (\<lambda>x n. True) (3) (2)
        (\<lambda>x n. [(if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1, (x n)!2]))"
      by (smt Id_def SimBlock_Id SimBlock_FBlock_parallel_comp add.commute f5_0 f5_1 one_add_one 
        one_plus_numeral semiring_norm(3) simblock_f3)
    (* ((((Min2 ;; UnitDelay 0) \<parallel>\<^sub>B (Const 1)) ;; Sum2) \<parallel>\<^sub>B Id \<parallel>\<^sub>B (Const 0)) *)
    have f6: "((((Min2 ;; UnitDelay 0) \<parallel>\<^sub>B (Const 1)) ;; Sum2) \<parallel>\<^sub>B Id \<parallel>\<^sub>B (Const 0))
      = (FBlock (\<lambda>x n. True) (3) (2)
          (\<lambda>x n. [(if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1, (x n)!2])) 
        \<parallel>\<^sub>B (Const 0)"
      using f5 f5_0 f5_1 by auto
    then have f6_0: "... = (FBlock (\<lambda>x n. True) (3) (3)
        (\<lambda>x n. ((((\<lambda>x n. [(if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1, (x n)!2])
                   \<circ> (\<lambda>xx nn. take 3 (xx nn))) x n) 
             @ (((f_Const 0) \<circ> (\<lambda>xx nn. drop 3 (xx nn)))) x n)))"
      using simblock_f5 SimBlock_Const by (simp add: FBlock_parallel_comp f_sim_blocks)
    then have f6_1: "... = (FBlock (\<lambda>x n. True) (3) (3)
          (\<lambda>x n. [(if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1, (x n)!2, 0]))"
      proof -
        have 11: "\<forall>inouts\<^sub>v x. ((f_Const 0 (\<lambda>nn. drop 3 (inouts\<^sub>v nn)) x)) = [0]"
          by (simp add: f_Const_def)
        have 12: "\<forall>inouts\<^sub>v x. length(inouts\<^sub>v x) = 3 \<longrightarrow> (take 3 (inouts\<^sub>v x)) = inouts\<^sub>v (x)"
          by simp
        (*
        have "\<forall>(inouts\<^sub>v::nat \<Rightarrow> real list) x::nat. \<forall>(y::nat). (((length(inouts\<^sub>v y) = 3) \<and> 
                x > 0) \<longrightarrow> (take 3 (inouts\<^sub>v (x - Suc 0)) = inouts\<^sub>v (x - Suc 0)))"
          apply (auto)
          sledgehammer
        sorry
        then have 2: "\<forall>inouts\<^sub>v x. 
          ((min (hd (take 3 (inouts\<^sub>v (x - Suc 0)))) (hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) + 1) #
            inouts\<^sub>v x!(2) # (f_Const 0 (\<lambda>nn. drop 3 (inouts\<^sub>v nn)) x)) =
            [min (hd (inouts\<^sub>v (x - Suc 0))) (hd (tl (inouts\<^sub>v (x - Suc 0)))) + 1, inouts\<^sub>v x!(2), 0]"
        sorry
        *)
        show "FBlock (\<lambda>x n. True) 3 3
              (\<lambda>x n. ((\<lambda>x n. [(if n = 0 then 0 else min (hd (x (n - 1))) (hd (tl (x (n - 1))))) + 1, x n!(2)]) \<circ>
                    (\<lambda>xx nn. take 3 (xx nn))) x n @ (f_Const 0 \<circ> (\<lambda>xx nn. drop 3 (xx nn))) x n) 
           = FBlock (\<lambda>x n. True) 3 3 (\<lambda>x n. [(if n = 0 then 0 else min (hd (x (n - 1))) 
                  (hd (tl (x (n - 1))))) + 1, x n!(2), 0])"
          apply (simp add: FBlock_def)
          apply (rel_auto)
          apply (simp add: f_Const_def)
          proof -
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::nat
            assume a1: "\<forall>x. (x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 3 \<and>
              length(inouts\<^sub>v' 0) = 3 \<and> 1 # inouts\<^sub>v 0!(2) # f_Const 0 (\<lambda>nn. drop 3 (inouts\<^sub>v nn)) 0 = inouts\<^sub>v' 0) \<and>
             (0 < x \<longrightarrow>
              length(inouts\<^sub>v x) = 3 \<and>
              length(inouts\<^sub>v' x) = 3 \<and>
              (min (hd (take 3 (inouts\<^sub>v (x - Suc 0)))) (hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) + 1) #
              inouts\<^sub>v x!(2) # f_Const 0 (\<lambda>nn. drop 3 (inouts\<^sub>v nn)) x =
              inouts\<^sub>v' x)"
            assume a2: "0 < x"
            from a1 have 1: "\<forall>x. length(inouts\<^sub>v x) = 3"
              using gr0I by blast
            from a2 a1 have 2: "
              (min (hd (take 3 (inouts\<^sub>v (x - Suc 0)))) (hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) + 1) #
              inouts\<^sub>v x!(2) # f_Const 0 (\<lambda>nn. drop 3 (inouts\<^sub>v nn)) x = inouts\<^sub>v' x"
              by blast
            from a2 1 have 3: "take 3 (inouts\<^sub>v (x - Suc 0)) = inouts\<^sub>v (x - Suc 0)"
              by simp
            show "[min (hd (inouts\<^sub>v (x - Suc 0))) (hd (tl (inouts\<^sub>v (x - Suc 0)))) + 1, inouts\<^sub>v x!(2), 0] = inouts\<^sub>v' x"
              by (metis "1" "11" "2" order_refl take_all)
          next
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list"
            assume a1: "\<forall>x. (x = 0 \<longrightarrow> length(inouts\<^sub>v 0) = 3 \<and> length(inouts\<^sub>v' 0) = 3 \<and> [1, inouts\<^sub>v 0!(2), 0] = inouts\<^sub>v' 0) \<and>
               (0 < x \<longrightarrow>
                length(inouts\<^sub>v x) = 3 \<and>
                length(inouts\<^sub>v' x) = 3 \<and>
                [min (hd (inouts\<^sub>v (x - Suc 0))) (hd (tl (inouts\<^sub>v (x - Suc 0)))) + 1, inouts\<^sub>v x!(2), 0] =
                inouts\<^sub>v' x)"
            show "1 # inouts\<^sub>v 0!(2) # f_Const 0 (\<lambda>nn. drop 3 (inouts\<^sub>v nn)) 0 = inouts\<^sub>v' 0"
              by (simp add: "11" a1)
          next
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::nat
            assume a1: "\<forall>x. (x = 0 \<longrightarrow> length(inouts\<^sub>v 0) = 3 \<and> length(inouts\<^sub>v' 0) = 3 \<and> [1, inouts\<^sub>v 0!(2), 0] = inouts\<^sub>v' 0) \<and>
               (0 < x \<longrightarrow>
                length(inouts\<^sub>v x) = 3 \<and>
                length(inouts\<^sub>v' x) = 3 \<and>
                [min (hd (inouts\<^sub>v (x - Suc 0))) (hd (tl (inouts\<^sub>v (x - Suc 0)))) + 1, inouts\<^sub>v x!(2), 0] =
                inouts\<^sub>v' x)"
            assume a2: "x > 0"
            from a1 have 1: "\<forall>x. length(inouts\<^sub>v x) = 3"
              using gr0I by blast
            from a2 1 have 3: "take 3 (inouts\<^sub>v (x - Suc 0)) = inouts\<^sub>v (x - Suc 0)"
              by simp
            show "(min (hd (take 3 (inouts\<^sub>v (x - Suc 0)))) (hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) + 1) #
               inouts\<^sub>v x!(2) # f_Const 0 (\<lambda>nn. drop 3 (inouts\<^sub>v nn)) x =
               inouts\<^sub>v' x"
              by (simp add: "11" "3" a1 a2)
          next
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" 
                and x::"nat\<Rightarrow>real list" and xa::nat
            show "length(f_Const 0 (\<lambda>nn. drop 3 (x nn)) xa) = Suc 0"
              by (simp add: f_Const_def)
          qed
      qed
    have simblock_f6: "SimBlock 3 3 (FBlock (\<lambda>x n. True) (3) (3)
          (\<lambda>x n. [(if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1, (x n)!2, 0]))"
      using Const_def simblock_f5 SimBlock_FBlock_parallel_comp
      by (metis (no_types, lifting) One_nat_def SimBlock_Const Suc3_eq_add_3 add.commute 
          add_2_eq_Suc' f6_0 f6_1 numeral_3_eq_3)
    (* ((((Min2 ;; UnitDelay 0) \<parallel>\<^sub>B (Const 1)) ;; Sum2) \<parallel>\<^sub>B Id \<parallel>\<^sub>B (Const 0)) ;; (Switch1 0.5) *)
    have f7: "((((Min2 ;; UnitDelay 0) \<parallel>\<^sub>B (Const 1)) ;; Sum2) \<parallel>\<^sub>B Id \<parallel>\<^sub>B (Const 0)) ;; (Switch1 0.5)
        = (FBlock (\<lambda>x n. True) (3) (3) (\<lambda>x n. [(if n = 0 then 0 else 
            (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1, (x n)!2, 0])) ;; (Switch1 0.5)"
      using f6 f6_0 f6_1 by auto
    have f7_0: "... = (FBlock (\<lambda>x n. True) (3) 1 ((f_Switch1 0.5) o (\<lambda>x n. [(if n = 0 then 0 else 
            (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1, (x n)!2, 0])))"
      using simblock_f6 SimBlock_Switch1 by (simp add: FBlock_seq_comp Switch1_def) 
    have f7_1: "... = FBlock (\<lambda>x n. True) (3) 1 
        (\<lambda>x n. [if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1)
          else 0])"
      proof -
        have 1: "\<forall>x n. (((f_Switch1 0.5) o (\<lambda>x n. [(if n = 0 then 0 else 
            (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1, (x n)!2, 0])) x n 
          =
            (\<lambda>x n. [if (x n)!2 \<ge> 0.5 
            then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1)
            else 0]) x n)"
          apply (auto)
          by (simp add: f_Switch1_def)+
        then show ?thesis
          by presburger
      qed
    have simblock_f7: "SimBlock 3 1 (FBlock (\<lambda>x n. True) (3) 1 
        (\<lambda>x n. [if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0]))"
      using simblock_f6 SimBlock_Switch1 SimBlock_FBlock_seq_comp f7 f7_0 f7_1
      by (metis (no_types, lifting) Switch1_def)
    (* ((((Min2 ;; UnitDelay 0) \<parallel>\<^sub>B (Const 1)) ;; Sum2) \<parallel>\<^sub>B Id \<parallel>\<^sub>B (Const 0)) ;; (Switch1 0.5) ;; Split2 *)
    have f8: "((((Min2 ;; UnitDelay 0) \<parallel>\<^sub>B (Const 1)) ;; Sum2) \<parallel>\<^sub>B Id \<parallel>\<^sub>B (Const 0)) ;; 
              (Switch1 0.5) ;; Split2 = 
        ((FBlock (\<lambda>x n. True) (3) 1 (\<lambda>x n. [if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0])) ;; Split2)"
      by (metis RA1 f7 f7_0 f7_1)
    have f8_0: "... = (FBlock (\<lambda>x n. True) (3) 2 (f_Split2 o (\<lambda>x n. [if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0])))"
      using simblock_f7 SimBlock_Split2
      by (simp add: FBlock_seq_comp Split2_def)
    have f8_1: "... = (FBlock (\<lambda>x n. True) (3) 2 (\<lambda>x n. [if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
          if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0]))"
      proof -
        have 11: "\<forall>x n. ((f_Split2 o (\<lambda>x n. [if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0])) x n) 
          = (\<lambda>x n. [if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
          if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0]) x n"
          apply (auto)
          by (simp add: f_Split2_def)+
         show ?thesis
           using 11 by presburger
      qed
    have simblock_f8: "SimBlock 3 2 (FBlock (\<lambda>x n. True) (3) 2 (\<lambda>x n. [if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
          if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0]))"
      using simblock_f7 f8 f8_0 f8_1 SimBlock_Split2 
      by (metis (no_types, lifting) SimBlock_FBlock_seq_comp Split2_def)
    show ?thesis
      using f8 f8_0 f8_1 by auto
  qed

(* 
one input: (2 \<longrightarrow> protect1)
two outputs: (13 \<longrightarrow> varConfirm_1), (13 \<longrightarrow> 14)
*)
abbreviation "variableTimer2 \<equiv>
  ((Const 0) \<parallel>\<^sub>B Id) ;; Max2 ;; (Gain Rate) ;; RoundCeil ;; DataTypeConvInt32Zero ;; Split2"

text {* @{text "variableTimer2"} is also simplified by @{text "variableTimer2_simp"}. *}
lemma variableTimer2_simp: 
  "variableTimer2 = (FBlock (\<lambda>x n. True) (Suc 0) (2) 
      (\<lambda>x n. [real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>))),
              real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>)))]))"
  proof -
    (* ((Const 0) \<parallel>\<^sub>B Id) *)
    have f1: "((Const 0) \<parallel>\<^sub>B Id) = (FBlock (\<lambda>x n. True) (1) (2) 
        (\<lambda>x n. ((((f_Const 0) \<circ> (\<lambda>xx nn. take 0 (xx nn))) x n) @ ((f_Id \<circ> (\<lambda>xx nn. drop 0 (xx nn)))) x n)))"
      using SimBlock_Const SimBlock_Id apply (simp add: FBlock_parallel_comp f_sim_blocks)
      by (simp add: numeral_2_eq_2)
    then have f1_0: "... = FBlock (\<lambda>x n. True) (Suc 0) 2 (\<lambda>x n. [0, hd(x n)])"
      by (simp add: f_blocks)
    have simblock_f1: "SimBlock (Suc 0) 2 (FBlock (\<lambda>x n. True) (Suc 0) 2 (\<lambda>x n. [0, hd(x n)]))"
      using SimBlock_Const SimBlock_Id SimBlock_FBlock_seq_comp
      by (metis (no_types, lifting) "f1" "f1_0" Const_def Id_def SimBlock_FBlock_parallel_comp Suc_eq_plus1 nat_1_add_1)
    (* ((Const 0) \<parallel>\<^sub>B Id) ;; Max2 *)
    have f2: "((Const 0) \<parallel>\<^sub>B Id) ;; Max2 = FBlock (\<lambda>x n. True) (Suc 0) 2 (\<lambda>x n. [0, hd(x n)]) ;; Max2"
      using f1_0 by (simp add: "f1")
    have f2_0: "... = FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) (f_Max2 o (\<lambda>x n. [0, hd(x n)]))"
      using simblock_f1 SimBlock_Max2 by (simp add: FBlock_seq_comp f_sim_blocks)
    have f2_1: "... = FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) (\<lambda>x n. [max (hd(x n)) 0])"
      using f_Max2_def
      by (metis (mono_tags, lifting) comp_eq_dest_lhs list.sel(1) list.sel(3) max.commute)
    have simblock_f2: "SimBlock (Suc 0) (Suc 0) (FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) (\<lambda>x n. [max (hd(x n)) 0]))"
      using simblock_f1 SimBlock_Max2 SimBlock_FBlock_seq_comp
      by (metis Max2_def One_nat_def f2_0 f2_1)
    have f3: "((Const 0) \<parallel>\<^sub>B Id) ;; Max2 ;; (Gain Rate) = 
          (FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) (\<lambda>x n. [max (hd(x n)) 0])) ;; (Gain Rate)"
      using f2_1 f2_0 by (simp add: RA1 f2)
    then have f3_0: "... = FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) ((f_Gain Rate) o (\<lambda>x n. [max (hd(x n)) 0]))"
      using SimBlock_Gain simblock_f2 by (simp add: FBlock_seq_comp f_sim_blocks)
    then have f3_1: "... = FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) (\<lambda>x n. [Rate * (max (hd(x n)) 0)])"
    proof -
      have "\<forall>f n. (f_Gain Rate \<circ> (\<lambda>f n. [max (hd (f n)) 0])) f n = [Rate * max (hd (f n)) 0]"
        by (simp add: f_Gain_def)
      then show ?thesis
        by presburger
    qed 
    have simblock_f3: "SimBlock (Suc 0) (Suc 0) 
            (FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) (\<lambda>x n. [Rate * (max (hd(x n)) 0)]))"
      using simblock_f2 SimBlock_Gain SimBlock_FBlock_seq_comp
      by (metis Gain_def One_nat_def f3_0 f3_1)
    (* ((Const 0) \<parallel>\<^sub>B Id) ;; Max2 ;; (Gain Rate) ;; RoundCeil *)
    have f4: "((Const 0) \<parallel>\<^sub>B Id) ;; Max2 ;; (Gain Rate) ;; RoundCeil = 
      (FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) (\<lambda>x n. [Rate * (max (hd(x n)) 0)])) ;; RoundCeil"
      using f3_0 f3_1 by (simp add: RA1 f2 f2_0 f2_1)
    then have f4_0: "... = (FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) (
            (f_RoundCeil) o (\<lambda>x n. [Rate * (max (hd(x n)) 0)])))"
      using SimBlock_RoundCeil simblock_f3 by (simp add: FBlock_seq_comp RoundCeil_def)
    then have f4_1: "... = (FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) (
            (\<lambda>x n. [real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>])))"
    proof -
      have "\<forall>f n. (f_RoundCeil \<circ> (\<lambda>f n. [Rate * max (hd (f n)) 0])) f n = [real_of_int \<lceil>Rate * max (hd (f n)) 0\<rceil>]"
        by (simp add: f_RoundCeil_def)
      then show ?thesis
        by presburger
    qed
    have simblock_f4: "SimBlock (Suc 0) (Suc 0) 
            (FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) ((\<lambda>x n. [real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>])))"
      using simblock_f3 SimBlock_RoundCeil SimBlock_FBlock_seq_comp
      by (metis One_nat_def RoundCeil_def f4_0 f4_1)
    (* ((Const 0) \<parallel>\<^sub>B Id) ;; Max2 ;; (Gain Rate) ;; RoundCeil ;; DataTypeConvInt32Zero *)
    have f5: "((Const 0) \<parallel>\<^sub>B Id) ;; Max2 ;; (Gain Rate) ;; RoundCeil ;; DataTypeConvInt32Zero
      = (FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) (\<lambda>x n. [real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>])) 
        ;; DataTypeConvInt32Zero"
      by (metis RA1 f4 f4_0 f4_1)
    then have f5_0: "... = (FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) 
                  (f_DTConvInt32Zero o (\<lambda>x n. [real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>])))"
      by (metis DataTypeConvInt32Zero_def One_nat_def FBlock_seq_comp 
          SimBlock_DataTypeConvInt32Zero simblock_f4)
    then have f5_1: "... = (FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) 
                  (\<lambda>x n. [real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>)))]))"
    proof -
      have "\<forall>f n. (f_DTConvInt32Zero \<circ> (\<lambda>f n. [real_of_int \<lceil>(Rate::real) * max (hd (f n)) 0\<rceil>])) f n 
                  = [real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (f n)) 0\<rceil>)))]"
        by (simp add: f_DTConvInt32Zero_def)
      then show ?thesis
        by presburger
    qed
    have simblock_f5: "SimBlock (Suc 0) (Suc 0) ((FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) 
                  (\<lambda>x n. [real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>)))])))"
      by (metis DataTypeConvInt32Zero_def One_nat_def SimBlock_DataTypeConvInt32Zero 
                SimBlock_FBlock_seq_comp f5_0 f5_1 simblock_f4)
    (* ((Const 0) \<parallel>\<^sub>B Id) ;; Max2 ;; (Gain Rate) ;; RoundCeil ;; DataTypeConvInt32Zero ;; Split2 *)
    have f6: "((Const 0) \<parallel>\<^sub>B Id) ;; Max2 ;; (Gain Rate) ;; RoundCeil ;; DataTypeConvInt32Zero ;; Split2
       = ((FBlock (\<lambda>x n. True) (Suc 0) (Suc 0) 
                  (\<lambda>x n. [real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>)))])))
         ;; Split2"
      by (metis RA1 f5 f5_0 f5_1)
    then have f6_0: "... = (FBlock (\<lambda>x n. True) (Suc 0) (2) 
      (f_Split2 o (\<lambda>x n. [real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>)))])))"
      by (metis Split2_def One_nat_def FBlock_seq_comp 
          SimBlock_Split2 simblock_f5)
    then have f6_1: "... = (FBlock (\<lambda>x n. True) (Suc 0) (2) 
      (\<lambda>x n. [real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>))),
              real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>)))]))"
    proof -
      have "\<forall>f n. [real_of_int (int32 (RoundZero (real_of_int \<lceil>(Rate::real) * max (hd (f n)) 0\<rceil>))), 
                   real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (f n)) 0\<rceil>)))] = 
          (f_Split2 \<circ> (\<lambda>f n. [real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (f n)) 0\<rceil>)))])) f n"
        by (simp add: f_Split2_def)
      then show ?thesis
        by presburger
    qed
    have simblock_f6: "SimBlock 1 2 (FBlock (\<lambda>x n. True) (Suc 0) (2) 
      (\<lambda>x n. [real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>))),
              real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>)))]))"
      by (metis (no_types, lifting) One_nat_def SimBlock_FBlock_seq_comp SimBlock_Split2 
        Split2_def f6_0 f6_1 simblock_f5)
    show ?thesis
      by (simp add: f6 f6_0 f6_1)
qed

text {* The @{text "variableTimer"} subsystem is composed of two parts by means of parallel composition 
and feedback. *}
definition "variableTimer \<equiv> 
  (((variableTimer1 \<parallel>\<^sub>B variableTimer2) f\<^sub>D (0,0))  f\<^sub>D (0,2)) ;; RopGT"

text {* @{text "vT_fd_sol_1"} calculates the output from its current and past inputs recursively. It
 is a solution for the first feedback in @{text "variableTimer"}. *}
(* (SOME (xx::nat \<Rightarrow> real). (xx n = (if (x n)!1 \<ge> 0.5 
              then ((if n = 0 then 0 else (min (xx (n-1)) (hd(x (n-1))))) + 1) else 0))) *)
(* calculate current output according to previous inputs *)
fun vT_fd_sol_1:: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
"vT_fd_sol_1 door_open_time door_open 0 = 
    (if door_open 0 \<ge> 0.5 then 1.0 else 0 )" |
"vT_fd_sol_1 door_open_time door_open (Suc n) = 
    (if door_open (Suc n) \<ge> 0.5 
     then ((min (vT_fd_sol_1 door_open_time door_open n) (door_open_time n)) + 1) 
     else 0)"

text {* @{text "vT_fd_sol_1"} is proved to be a solution for the first feedback. This lemma will be 
used later to expand the first feedback. *}
lemma vT_fd_sol_1_is_a_solution:
  fixes inouts\<^sub>0::"nat \<Rightarrow> real list" and n::nat
  assumes a1: "\<forall>x. length(inouts\<^sub>0 x) = 3"
  shows "0 < n \<longrightarrow> (1 \<le> inouts\<^sub>0 n!(Suc 0) * 2 \<longrightarrow>
        vT_fd_sol_1 (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) n =
        min (vT_fd_sol_1 (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (n - Suc 0))
         (hd (inouts\<^sub>0 (n - Suc 0))) + 1) \<and>
       (\<not> 1 \<le> inouts\<^sub>0 n!(Suc 0) * 2 \<longrightarrow>
        vT_fd_sol_1 (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) n = 0)"
  apply (clarify, rule conjI, clarify)
  defer
  apply (clarify)
  proof -
    assume a1: "0 < n"
    assume a2: "\<not> 1 \<le> inouts\<^sub>0 n!(Suc 0) * 2"
    from a2 have a2': "inouts\<^sub>0 n!(Suc 0) < 0.5"
      by (simp)
    have 1: "vT_fd_sol_1 (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) n
      = vT_fd_sol_1 (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (Suc (n - Suc 0))"
      using a1 by simp
    show "vT_fd_sol_1 (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) n = 0"
      apply (simp add: "1")
      using a2' by (simp add: a1)
  next
    assume a1: "0 < n"
    assume a2: "1 \<le> inouts\<^sub>0 n!(Suc 0) * 2"
    from a2 have a2': "inouts\<^sub>0 n!(Suc 0) \<ge> 0.5"
      by (simp)
    have 1: "vT_fd_sol_1 (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) n
      = vT_fd_sol_1 (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (Suc (n - Suc 0))"
      using a1 by simp
    show "vT_fd_sol_1 (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) n =
      min (vT_fd_sol_1 (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (n - Suc 0))
      (hd (inouts\<^sub>0 (n - Suc 0))) + 1"
      apply (simp add: "1")
      using a2' a1 by simp
  qed

text {* @{text "variableTimer_simp_pat_f"} gives the function definition of the finally simplified 
subsystem. *}
abbreviation "variableTimer_simp_pat_f 
  \<equiv> (\<lambda>x na. [if (if 1 \<le> x na!(0) * 2
          then (if na = 0 then 0
                else min (vT_fd_sol_1
                           (\<lambda>n1. (\<lambda>na. real_of_int
                                  (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) n1)
                           (\<lambda>n1. (x n1)!(0)) (na - 1))
                      ((\<lambda>na. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>))))
                            (na - 1))) + 1
          else 0) > (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) 
          then 1 else 0])"

text {* @{text "variableTimer_simp_pat"} is the simplified block for the subsystem. *}
abbreviation "variableTimer_simp_pat 
  \<equiv> (FBlock (\<lambda>x n. True) (2) 1 variableTimer_simp_pat_f)"

text {* @{text "variableTimer_simp_pat"} is also a block. *}
lemma SimBlock_variableTimer_simp: 
   "SimBlock 2 1 variableTimer_simp_pat"
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [0, 0]" in exI)
  apply (rule_tac x = "\<lambda>na. [0]" in exI)
  apply (simp)
  apply (simp add: int32_def RoundZero_def)
  by simp
  
text {* @{text "variableTimer_simp"} simplifies the subsystem into a block. *}
lemma variableTimer_simp:
  "variableTimer = variableTimer_simp_pat"
  proof -
    let ?vt_f = "(\<lambda>x na. [if (if 1 \<le> x na!(0) * 2
          then (if na = 0 then 0
                else min (vT_fd_sol_1
                           (\<lambda>n1. (\<lambda>na. real_of_int
                                  (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) n1)
                           (\<lambda>n1. (x n1)!(0)) (na - 1))
                      ((\<lambda>na. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>))))
                            (na - 1))) + 1
          else 0) > (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) 
          then 1 else 0])"
    (* (variableTimer1 \<parallel>\<^sub>B variableTimer2) *)
    have simblock_variableTimer1: "SimBlock 3 2 (FBlock (\<lambda>x n. True) (3) 2 (\<lambda>x n. [if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
          if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0]))"
      apply (simp add: SimBlock_def FBlock_def)
      apply (rel_auto)
      apply (rule_tac x = "\<lambda>na. [2, 1, 0.51]" in exI, simp)
      apply (rule_tac x = "\<lambda>na. (if na = 0 then [1,1] else [2,2])" in exI)
      by (simp)
    have simblock_variableTimer2: "SimBlock (Suc 0) 2 (FBlock (\<lambda>x n. True) (Suc 0) (2) 
          (\<lambda>x n. [real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>))),
              real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>)))]))"
      apply (simp add: SimBlock_def FBlock_def)
      apply (rel_auto)
      apply (rule_tac x = "\<lambda>na. [1]" in exI, simp)
      apply (rule_tac x = "\<lambda>na. [Rate,Rate]" in exI, simp)
      by (simp add: RoundZero_def int32_def)
    have f1: "(variableTimer1 \<parallel>\<^sub>B variableTimer2) 
      = (FBlock (\<lambda>x n. True) (3) 2 (\<lambda>x n. [if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
          if (x n)!2 \<ge> 0.5 
          then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0]))
         \<parallel>\<^sub>B 
        (FBlock (\<lambda>x n. True) (Suc 0) (2) 
          (\<lambda>x n. [real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>))),
              real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>)))]))"
      using variableTimer1_simp variableTimer2_simp by auto
    then have f1_0: "... = (FBlock (\<lambda>x n. True) (4) 4 
      (\<lambda>x n. ((((\<lambda>x n. 
                [if (x n)!2 \<ge> 0.5 
                  then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
                  if (x n)!2 \<ge> 0.5 
                  then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0])
              \<circ> (\<lambda>xx nn. take 3 (xx nn))) x n)
            @ (((\<lambda>x n. [real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>))),
              real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>)))])
              \<circ> (\<lambda>xx nn. drop 3 (xx nn)))) x n)))"
      using simblock_variableTimer1 simblock_variableTimer2 by (simp add: FBlock_parallel_comp f_sim_blocks)
    then have f1_1: "... = (FBlock (\<lambda>x n. True) (4) 4 
      ((\<lambda>x n. 
          [if (x n)!2 \<ge> 0.5 
            then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
            if (x n)!2 \<ge> 0.5 
            then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
            real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max ((x n)!3) 0)\<rceil>))),
            real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max ((x n)!3) 0)\<rceil>)))])))"
      proof -
        have 11: "\<forall>x n. ((length(x n) = 4) \<longrightarrow> ((\<lambda>x n. ((((\<lambda>x n. 
                [if (x n)!2 \<ge> 0.5 
                  then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
                  if (x n)!2 \<ge> 0.5 
                  then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0])
              \<circ> (\<lambda>xx nn. take 3 (xx nn))) x n)
            @ (((\<lambda>x n. [real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>))),
              real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max (hd(x n)) 0)\<rceil>)))])
              \<circ> (\<lambda>xx nn. drop 3 (xx nn)))) x n)) x n)
          = ((\<lambda>x n. 
          [if (x n)!2 \<ge> 0.5 
            then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
            if (x n)!2 \<ge> 0.5 
            then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
            real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max ((x n)!3) 0)\<rceil>))),
            real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max ((x n)!3) 0)\<rceil>)))]) x n))"
          apply (auto)
          apply (simp add: hd_drop_conv_nth)
          apply (smt diff_Suc_1 hd_conv_nth list.sel(2) nth_take numeral_3_eq_3 take_eq_Nil tl_take 
            zero_less_Suc zero_neq_numeral)
          apply (metis eval_nat_numeral(2) hd_drop_conv_nth lessI semiring_norm(26) semiring_norm(27))
          by (metis eval_nat_numeral(2) hd_drop_conv_nth lessI semiring_norm(26) semiring_norm(27))
        show ?thesis
          apply (simp add: FBlock_def)
          apply (rel_simp)
          apply (rule iffI)
          apply (clarify)
          apply (rule conjI)
          apply (clarify)
          apply (rule conjI)
          apply (clarify)
          apply (metis eval_nat_numeral(2) hd_drop_conv_nth lessI semiring_norm(26) semiring_norm(27))
          apply (metis eval_nat_numeral(2) hd_drop_conv_nth lessI semiring_norm(26) semiring_norm(27))
          apply (clarify)
          apply (rule conjI)
          apply (clarify)
          apply (rule conjI)
          apply blast
          apply (rule conjI)
          apply blast
          proof -
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" 
                and x::"nat"
            assume a1: "\<forall>x. (x = 0 \<longrightarrow>
              (1 \<le> inouts\<^sub>v 0!(2) * 2 \<longrightarrow>
               length(inouts\<^sub>v 0) = 4 \<and>
               length(inouts\<^sub>v' 0) = 4 \<and>
               [1, 1, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v 0))) 0\<rceil>))),
                real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v 0))) 0\<rceil>)))] =
               inouts\<^sub>v' 0) \<and>
              (\<not> 1 \<le> inouts\<^sub>v 0!(2) * 2 \<longrightarrow>
               length(inouts\<^sub>v 0) = 4 \<and>
               length(inouts\<^sub>v' 0) = 4 \<and>
               [0, 0, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v 0))) 0\<rceil>))),
                real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v 0))) 0\<rceil>)))] =
               inouts\<^sub>v' 0)) \<and>
             (0 < x \<longrightarrow>
              (1 \<le> inouts\<^sub>v x!(2) * 2 \<longrightarrow>
               length(inouts\<^sub>v x) = 4 \<and>
               length(inouts\<^sub>v' x) = 4 \<and>
               [min (hd (take 3 (inouts\<^sub>v (x - Suc 0)))) (hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) + 1,
                min (hd (take 3 (inouts\<^sub>v (x - Suc 0)))) (hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) + 1,
                real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>))),
                real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>)))] =
               inouts\<^sub>v' x) \<and>
              (\<not> 1 \<le> inouts\<^sub>v x!(2) * 2 \<longrightarrow>
               length(inouts\<^sub>v x) = 4 \<and>
               length(inouts\<^sub>v' x) = 4 \<and>
               [0, 0, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>))),
                real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>)))] =
               inouts\<^sub>v' x))"
            assume a2: "0 < x"
            assume a3: "1 \<le> inouts\<^sub>v x!(2) * 2"
            from a1 have 11: "\<forall>x. length(inouts\<^sub>v x) = 4"
              using a2 by blast
            have 12: "hd(drop 3 (inouts\<^sub>v x)) = (inouts\<^sub>v x!(3))"
              using 11 by (simp add: hd_drop_conv_nth)
            have 13: "(hd (take 3 (inouts\<^sub>v (x - Suc 0)))) = (hd (inouts\<^sub>v (x - Suc 0)))"
              using a1 by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
            have 14: "(hd (take 3 (inouts\<^sub>v (x - Suc 0)))) = (hd (inouts\<^sub>v (x - Suc 0)))"
              using a1 by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
            have 15: "(hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) = (hd (tl (inouts\<^sub>v (x - Suc 0))))"
              by (metis Zero_not_Suc append_take_drop_id hd_append2 numeral_3_eq_3 take_eq_Nil take_tl)
            show "[min (hd (inouts\<^sub>v (x - Suc 0))) (hd (tl (inouts\<^sub>v (x - Suc 0)))) + 1,
              min (hd (inouts\<^sub>v (x - Suc 0))) (hd (tl (inouts\<^sub>v (x - Suc 0)))) + 1,
              real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(3)) 0\<rceil>))),
              real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(3)) 0\<rceil>)))] =
              inouts\<^sub>v' x"
              using 11 12 13 14 15 by (metis a1 a2 a3)
          next
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" 
              and x::"nat"
            assume a1: "\<forall>x. (x = 0 \<longrightarrow>
              (1 \<le> inouts\<^sub>v 0!(2) * 2 \<longrightarrow>
               length(inouts\<^sub>v 0) = 4 \<and>
               length(inouts\<^sub>v' 0) = 4 \<and>
               [1, 1, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v 0))) 0\<rceil>))),
                real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v 0))) 0\<rceil>)))] =
               inouts\<^sub>v' 0) \<and>
              (\<not> 1 \<le> inouts\<^sub>v 0!(2) * 2 \<longrightarrow>
               length(inouts\<^sub>v 0) = 4 \<and>
               length(inouts\<^sub>v' 0) = 4 \<and>
               [0, 0, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v 0))) 0\<rceil>))),
                real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v 0))) 0\<rceil>)))] =
               inouts\<^sub>v' 0)) \<and>
             (0 < x \<longrightarrow>
              (1 \<le> inouts\<^sub>v x!(2) * 2 \<longrightarrow>
               length(inouts\<^sub>v x) = 4 \<and>
               length(inouts\<^sub>v' x) = 4 \<and>
               [min (hd (take 3 (inouts\<^sub>v (x - Suc 0)))) (hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) + 1,
                min (hd (take 3 (inouts\<^sub>v (x - Suc 0)))) (hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) + 1,
                real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>))),
                real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>)))] =
               inouts\<^sub>v' x) \<and>
              (\<not> 1 \<le> inouts\<^sub>v x!(2) * 2 \<longrightarrow>
               length(inouts\<^sub>v x) = 4 \<and>
               length(inouts\<^sub>v' x) = 4 \<and>
               [0, 0, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>))),
                real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>)))] =
               inouts\<^sub>v' x))"
            have 11: "hd (drop 3 (inouts\<^sub>v x)) = inouts\<^sub>v x!(3)"
              by (metis a1 eval_nat_numeral(2) gr_zeroI hd_drop_conv_nth lessI semiring_norm(26) semiring_norm(27))
            show "\<not> 1 \<le> inouts\<^sub>v x!(2) * 2 \<longrightarrow>
               length(inouts\<^sub>v x) = 4 \<and>
               length(inouts\<^sub>v' x) = 4 \<and>
               [0, 0, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(3)) 0\<rceil>))),
                real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(3)) 0\<rceil>)))] =
                inouts\<^sub>v' x"
                apply (auto)
                using a1 gr_zeroI apply blast
                using a1 gr_zeroI apply blast
                by (metis "11" a1 neq0_conv)
          next
            show "\<And>ok\<^sub>v inouts\<^sub>v ok\<^sub>v' inouts\<^sub>v'.
             ok\<^sub>v \<longrightarrow>
             ok\<^sub>v' \<and>
             (\<forall>x. (x = 0 \<longrightarrow>
                   (1 \<le> inouts\<^sub>v 0!2 * 2 \<longrightarrow>
                    length(inouts\<^sub>v 0) = 4 \<and>
                    length(inouts\<^sub>v' 0) = 4 \<and>
                    [1, 1, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!3) 0\<rceil>))),
                     real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!3) 0\<rceil>)))] =
                    inouts\<^sub>v' 0) \<and>
                   (\<not> 1 \<le> inouts\<^sub>v 0!2 * 2 \<longrightarrow>
                    length(inouts\<^sub>v 0) = 4 \<and>
                    length(inouts\<^sub>v' 0) = 4 \<and>
                    [0, 0, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!3) 0\<rceil>))),
                     real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!3) 0\<rceil>)))] =
                    inouts\<^sub>v' 0)) \<and>
                  (0 < x \<longrightarrow>
                   (1 \<le> inouts\<^sub>v x!2 * 2 \<longrightarrow>
                    length(inouts\<^sub>v x) = 4 \<and>
                    length(inouts\<^sub>v' x) = 4 \<and>
                    [min (hd (inouts\<^sub>v (x - Suc 0))) (hd (tl (inouts\<^sub>v (x - Suc 0)))) + 1,
                     min (hd (inouts\<^sub>v (x - Suc 0))) (hd (tl (inouts\<^sub>v (x - Suc 0)))) + 1,
                     real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!3) 0\<rceil>))),
                     real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!3) 0\<rceil>)))] =
                    inouts\<^sub>v' x) \<and>
                   (\<not> 1 \<le> inouts\<^sub>v x!2 * 2 \<longrightarrow>
                    length(inouts\<^sub>v x) = 4 \<and>
                    length(inouts\<^sub>v' x) = 4 \<and>
                    [0, 0, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!3) 0\<rceil>))),
                     real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!3) 0\<rceil>)))] =
                    inouts\<^sub>v' x))) \<Longrightarrow>
             ok\<^sub>v \<longrightarrow>
             ok\<^sub>v' \<and>
             (\<forall>x. (x = 0 \<longrightarrow>
                   (1 \<le> inouts\<^sub>v 0!2 * 2 \<longrightarrow>
                    length(inouts\<^sub>v 0) = 4 \<and>
                    length(inouts\<^sub>v' 0) = 4 \<and>
                    [1, 1, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v 0))) 0\<rceil>))),
                     real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v 0))) 0\<rceil>)))] =
                    inouts\<^sub>v' 0) \<and>
                   (\<not> 1 \<le> inouts\<^sub>v 0!2 * 2 \<longrightarrow>
                    length(inouts\<^sub>v 0) = 4 \<and>
                    length(inouts\<^sub>v' 0) = 4 \<and>
                    [0, 0, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v 0))) 0\<rceil>))),
                     real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v 0))) 0\<rceil>)))] =
                    inouts\<^sub>v' 0)) \<and>
                  (0 < x \<longrightarrow>
                   (1 \<le> inouts\<^sub>v x!2 * 2 \<longrightarrow>
                    length(inouts\<^sub>v x) = 4 \<and>
                    length(inouts\<^sub>v' x) = 4 \<and>
                    [min (hd (take 3 (inouts\<^sub>v (x - Suc 0)))) (hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) + 1,
                     min (hd (take 3 (inouts\<^sub>v (x - Suc 0)))) (hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) + 1,
                     real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>))),
                     real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>)))] =
                    inouts\<^sub>v' x) \<and>
                   (\<not> 1 \<le> inouts\<^sub>v x!2 * 2 \<longrightarrow>
                    length(inouts\<^sub>v x) = 4 \<and>
                    length(inouts\<^sub>v' x) = 4 \<and>
                    [0, 0, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>))),
                     real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>)))] =
                    inouts\<^sub>v' x)))"
              apply (clarify)
              apply (rule conjI)
              apply (clarify)
              apply (rule conjI)
              apply (clarify)
              apply (rule conjI)
              apply blast
              apply (rule conjI)
              apply blast
              apply (metis eval_nat_numeral(2) hd_drop_conv_nth lessI semiring_norm(26) semiring_norm(27))
              apply (clarify)
              apply (rule conjI)
              apply blast
              apply (rule conjI)
              apply blast
              apply (metis eval_nat_numeral(2) hd_drop_conv_nth lessI semiring_norm(26) semiring_norm(27))
              apply (clarify)
              apply (rule conjI)
              apply (clarify)
              apply (rule conjI)
              apply blast
              apply (rule conjI)
              apply blast
              proof -
                fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" 
                    and x::"nat"
                assume a1: "\<forall>x. (x = 0 \<longrightarrow>
                  (1 \<le> inouts\<^sub>v 0!2 * 2 \<longrightarrow>
                   length(inouts\<^sub>v 0) = 4 \<and>
                   length(inouts\<^sub>v' 0) = 4 \<and>
                   [1, 1, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!3) 0\<rceil>))),
                    real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!3) 0\<rceil>)))] =
                   inouts\<^sub>v' 0) \<and>
                  (\<not> 1 \<le> inouts\<^sub>v 0!2 * 2 \<longrightarrow>
                   length(inouts\<^sub>v 0) = 4 \<and>
                   length(inouts\<^sub>v' 0) = 4 \<and>
                   [0, 0, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!3) 0\<rceil>))),
                    real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!3) 0\<rceil>)))] =
                   inouts\<^sub>v' 0)) \<and>
                 (0 < x \<longrightarrow>
                  (1 \<le> inouts\<^sub>v x!2 * 2 \<longrightarrow>
                   length(inouts\<^sub>v x) = 4 \<and>
                   length(inouts\<^sub>v' x) = 4 \<and>
                   [min (hd (inouts\<^sub>v (x - Suc 0))) (hd (tl (inouts\<^sub>v (x - Suc 0)))) + 1,
                    min (hd (inouts\<^sub>v (x - Suc 0))) (hd (tl (inouts\<^sub>v (x - Suc 0)))) + 1,
                    real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!3) 0\<rceil>))),
                    real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!3) 0\<rceil>)))] =
                   inouts\<^sub>v' x) \<and>
                  (\<not> 1 \<le> inouts\<^sub>v x!2 * 2 \<longrightarrow>
                   length(inouts\<^sub>v x) = 4 \<and>
                   length(inouts\<^sub>v' x) = 4 \<and>
                   [0, 0, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!3) 0\<rceil>))),
                    real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!3) 0\<rceil>)))] =
                   inouts\<^sub>v' x))"
                assume a2: "0 < x"
                assume a3: "1 \<le> inouts\<^sub>v x!(2) * 2"
                from a1 have 11: "\<forall>x. length(inouts\<^sub>v x) = 4"
                  using a2 by blast
                have 12: "hd(drop 3 (inouts\<^sub>v x)) = (inouts\<^sub>v x!(3))"
                  using 11 by (simp add: hd_drop_conv_nth)
                have 13: "(hd (take 3 (inouts\<^sub>v (x - Suc 0)))) = (hd (inouts\<^sub>v (x - Suc 0)))"
                  using a1 by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
                have 14: "(hd (take 3 (inouts\<^sub>v (x - Suc 0)))) = (hd (inouts\<^sub>v (x - Suc 0)))"
                  using a1 by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
                have 15: "(hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) = (hd (tl (inouts\<^sub>v (x - Suc 0))))"
                  by (metis Zero_not_Suc append_take_drop_id hd_append2 numeral_3_eq_3 take_eq_Nil take_tl)
                show "[min (hd (take 3 (inouts\<^sub>v (x - Suc 0)))) (hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) + 1,
                      min (hd (take 3 (inouts\<^sub>v (x - Suc 0)))) (hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) + 1,
                      real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>))),
                      real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>)))] =
                     inouts\<^sub>v' x"
                  using 11 12 13 14 15 by (metis a1 a2 a3)
              next
                fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" 
                    and x::"nat"
                assume a1: "\<forall>x. (x = 0 \<longrightarrow>
                  (1 \<le> inouts\<^sub>v 0!2 * 2 \<longrightarrow>
                   length(inouts\<^sub>v 0) = 4 \<and>
                   length(inouts\<^sub>v' 0) = 4 \<and>
                   [1, 1, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!3) 0\<rceil>))),
                    real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!3) 0\<rceil>)))] =
                   inouts\<^sub>v' 0) \<and>
                  (\<not> 1 \<le> inouts\<^sub>v 0!2 * 2 \<longrightarrow>
                   length(inouts\<^sub>v 0) = 4 \<and>
                   length(inouts\<^sub>v' 0) = 4 \<and>
                   [0, 0, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!3) 0\<rceil>))),
                    real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!3) 0\<rceil>)))] =
                   inouts\<^sub>v' 0)) \<and>
                 (0 < x \<longrightarrow>
                  (1 \<le> inouts\<^sub>v x!2 * 2 \<longrightarrow>
                   length(inouts\<^sub>v x) = 4 \<and>
                   length(inouts\<^sub>v' x) = 4 \<and>
                   [min (hd (inouts\<^sub>v (x - Suc 0))) (hd (tl (inouts\<^sub>v (x - Suc 0)))) + 1,
                    min (hd (inouts\<^sub>v (x - Suc 0))) (hd (tl (inouts\<^sub>v (x - Suc 0)))) + 1,
                    real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!3) 0\<rceil>))),
                    real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!3) 0\<rceil>)))] =
                   inouts\<^sub>v' x) \<and>
                  (\<not> 1 \<le> inouts\<^sub>v x!2 * 2 \<longrightarrow>
                   length(inouts\<^sub>v x) = 4 \<and>
                   length(inouts\<^sub>v' x) = 4 \<and>
                   [0, 0, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!3) 0\<rceil>))),
                    real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!3) 0\<rceil>)))] =
                   inouts\<^sub>v' x))"
                assume a2: "0 < x"
                from a1 have 11: "\<forall>x. length(inouts\<^sub>v x) = 4"
                  using a2 by blast
                have 12: "hd(drop 3 (inouts\<^sub>v x)) = (inouts\<^sub>v x!(3))"
                  using 11 by (simp add: hd_drop_conv_nth)
                have 13: "(hd (take 3 (inouts\<^sub>v (x - Suc 0)))) = (hd (inouts\<^sub>v (x - Suc 0)))"
                  using a1 by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
                have 14: "(hd (take 3 (inouts\<^sub>v (x - Suc 0)))) = (hd (inouts\<^sub>v (x - Suc 0)))"
                  using a1 by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
                have 15: "(hd (tl (take 3 (inouts\<^sub>v (x - Suc 0))))) = (hd (tl (inouts\<^sub>v (x - Suc 0))))"
                  by (metis Zero_not_Suc append_take_drop_id hd_append2 numeral_3_eq_3 take_eq_Nil take_tl)
                show "\<not> 1 \<le> inouts\<^sub>v x!(2) * 2 \<longrightarrow>
                   length(inouts\<^sub>v x) = 4 \<and>
                   length(inouts\<^sub>v' x) = 4 \<and>
                   [0, 0, real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>))),
                    real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (drop 3 (inouts\<^sub>v x))) 0\<rceil>)))] =
                   inouts\<^sub>v' x"
                  apply (clarify)
                  apply (rule conjI)
                  apply (simp add: "11")
                  apply (rule conjI)
                  using a1 a2 apply blast
                  using 11 12 13 14 15
                  by (simp add: a1 a2)
              qed
            qed
      qed
    have simblock_f1: "SimBlock 4 4 (FBlock (\<lambda>x n. True) (4) 4 
      ((\<lambda>x n. 
          [if (x n)!2 \<ge> 0.5 
            then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
            if (x n)!2 \<ge> 0.5 
            then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
            real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max ((x n)!3) 0)\<rceil>))),
            real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max ((x n)!3) 0)\<rceil>)))])))"
      using simblock_variableTimer1 simblock_variableTimer2
      by (metis (no_types, lifting) One_nat_def SimBlock_FBlock_parallel_comp Suc_eq_plus1 
        eval_nat_numeral(2) f1_0 f1_1 numeral_code(2) semiring_norm(26) semiring_norm(27))
    have inps_f1: "inps (FBlock (\<lambda>x n. True) (4) 4 
      ((\<lambda>x n. 
          [if (x n)!2 \<ge> 0.5 
            then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
            if (x n)!2 \<ge> 0.5 
            then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
            real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max ((x n)!3) 0)\<rceil>))),
            real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max ((x n)!3) 0)\<rceil>)))]))) = 4"
      using simblock_f1 using inps_P by blast
    have outps_f1: "outps (FBlock (\<lambda>x n. True) (4) 4 
      ((\<lambda>x n. 
          [if (x n)!2 \<ge> 0.5 
            then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
            if (x n)!2 \<ge> 0.5 
            then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
            real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max ((x n)!3) 0)\<rceil>))),
            real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max ((x n)!3) 0)\<rceil>)))]))) = 4"
      using simblock_f1 using outps_P by blast
    (* ((variableTimer1 \<parallel>\<^sub>B variableTimer2) f\<^sub>D (0,0)) *) 
    let ?f2_f = "((\<lambda>x n. 
          [if (x n)!2 \<ge> 0.5 
            then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
            if (x n)!2 \<ge> 0.5 
            then ((if n = 0 then 0 else (min (hd(x (n-1))) (hd(tl(x (n-1)))))) + 1) else 0,
            real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max ((x n)!3) 0)\<rceil>))),
            real_of_int (int32 (RoundZero(real_of_int \<lceil>Rate * (max ((x n)!3) 0)\<rceil>)))]))"
    let ?f2 = "(FBlock (\<lambda>x n. True) (4) 4 ?f2_f)"
    let ?f2_xx = "(\<lambda>(inouts\<^sub>0::nat \<Rightarrow> real list). \<lambda>na. vT_fd_sol_1 
                        (\<lambda>n1. hd(inouts\<^sub>0 n1)) (\<lambda>n1. (inouts\<^sub>0 n1)!1) na)"
    have f2: "((variableTimer1 \<parallel>\<^sub>B variableTimer2) f\<^sub>D (0,0))
      = ?f2 f\<^sub>D (0,0)"
      using f1 f1_0 f1_1 by auto
    have is_solution_f2: "is_Solution 0 0 4 4 ?f2_f ?f2_xx"
      apply (simp add: is_Solution_def)
      apply (rule allI)
      apply (simp add: f_PreFD_def)
      apply (clarify)
      using vT_fd_sol_1_is_a_solution by blast
    have unique_f2: "Solvable_unique 0 0 4 4 ?f2_f"
      apply (simp add: Solvable_unique_def)
      apply (rule allI, clarify, simp add: f_PreFD_def)
      apply (rule ex_ex1I)
      apply (rule_tac x = "\<lambda>na. vT_fd_sol_1 
                                  (\<lambda>n1. hd(inouts\<^sub>0 n1)) (\<lambda>n1. (inouts\<^sub>0 n1)!1) na" in exI)
      apply (simp)
      apply (rule allI)
      using vT_fd_sol_1_is_a_solution apply (simp)
      proof -
        fix inouts\<^sub>0::"nat \<Rightarrow> real list" and xx y ::"nat \<Rightarrow> real"
        assume a1: "\<forall>x. length(inouts\<^sub>0 x) = 3"
        assume a2: "\<forall>n. (n = 0 \<longrightarrow> (1 \<le> inouts\<^sub>0 0!(Suc 0) * 2 \<longrightarrow> xx 0 = 1) \<and> 
                                (\<not> 1 \<le> inouts\<^sub>0 0!(Suc 0) * 2 \<longrightarrow> xx 0 = 0)) \<and>
           (0 < n \<longrightarrow>
            (1 \<le> inouts\<^sub>0 n!(Suc 0) * 2 \<longrightarrow> xx n = min (xx (n - Suc 0)) (hd (inouts\<^sub>0 (n - Suc 0))) + 1) \<and>
            (\<not> 1 \<le> inouts\<^sub>0 n!(Suc 0) * 2 \<longrightarrow> xx n = 0))"
        assume a3: "\<forall>n. (n = 0 \<longrightarrow> (1 \<le> inouts\<^sub>0 0!(Suc 0) * 2 \<longrightarrow> y 0 = 1) \<and> 
                                (\<not> 1 \<le> inouts\<^sub>0 0!(Suc 0) * 2 \<longrightarrow> y 0 = 0)) \<and>
           (0 < n \<longrightarrow>
            (1 \<le> inouts\<^sub>0 n!(Suc 0) * 2 \<longrightarrow> y n = min (y (n - Suc 0)) (hd (inouts\<^sub>0 (n - Suc 0))) + 1) \<and>
            (\<not> 1 \<le> inouts\<^sub>0 n!(Suc 0) * 2 \<longrightarrow> y n = 0)) "
        have 1: "\<forall>n. xx n = y n"
          apply (rule allI)
          proof -
            fix n::nat
            show "xx n = y n"
              proof (induct n)
                case 0
                then show ?case 
                  using a2 a3 by metis
              next
                case (Suc n) note IH = this
                then show ?case
                  using a2 a3 by (metis One_nat_def diff_Suc_1 zero_less_Suc)
              qed
          qed
        show "xx = y"
          by (simp add: "1" fun_eq)
      qed
    let ?f3_f = "(\<lambda>x na. [if 1 \<le> x na!(Suc 0) * 2
              then (if na = 0 then 0
                    else min ((vT_fd_sol_1 (\<lambda>n1. hd (x n1)) (\<lambda>n1. x n1!(Suc 0))) (na - 1))
                          (hd (x (na - 1)))) + 1
              else 0,
              real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(2)) 0\<rceil>))),
              real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(2)) 0\<rceil>)))])"
    have f2_0: 
      "?f2 f\<^sub>D (0,0) = 
        (FBlock (\<lambda>x n. True) (4-1) (4-1)
            (\<lambda>x na. ((f_PostFD 0) 
            o ?f2_f
            o (f_PreFD (?f2_xx x) 0)) x na))"
      using is_solution_f2 unique_f2 simblock_f1 FBlock_feedback' by blast
    then have f2_1:
      "... = FBlock (\<lambda>x n. True) 3 3 ?f3_f"
      apply (simp (no_asm) add: f_PreFD_def f_PostFD_def)
      using f_PreFD_def 
      by (metis (lifting) append.left_neutral drop_0 f_PreFD_def list.sel(1) list.sel(3) take_0)
    have simblock_f2_0: "SimBlock (4-1) (4-1) (?f2 f\<^sub>D (0,0))"
      using simblock_f1 unique_f2 Solvable_unique_is_solvable SimBlock_FBlock_feedback by blast
    then have simblock_f2: "SimBlock 3 3 (FBlock (\<lambda>x n. True) 3 3 ?f3_f)"
      by (metis (no_types, lifting) Suc_eq_plus1 add_diff_cancel_right' eval_nat_numeral(2) f2_0 
          f2_1 semiring_norm(26) semiring_norm(27))
    have inps_f2: "inps (FBlock (\<lambda>x n. True) 3 3 ?f3_f) = 3"
      using simblock_f2 using inps_P by blast
    have outps_f2: "outps (FBlock (\<lambda>x n. True) 3 3 ?f3_f) = 3"
      using simblock_f2 using outps_P by blast
    (* (((variableTimer1 \<parallel>\<^sub>B variableTimer2) f\<^sub>D (0,0))  f\<^sub>D (0,2)) *)
    have f3: "(((variableTimer1 \<parallel>\<^sub>B variableTimer2) f\<^sub>D (0,0)) f\<^sub>D (0,2))
      = (FBlock (\<lambda>x n. True) 3 3 ?f3_f) f\<^sub>D (0,2)"
      using f2 f2_0 f2_1 by auto
    let ?f3_xx = "(\<lambda>(inouts\<^sub>0::nat \<Rightarrow> real list). \<lambda>na. 
      real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>0 na!(1)) 0\<rceil>))))"
    have is_solution_f3: "is_Solution 0 2 3 3 ?f3_f ?f3_xx"
      apply (simp add: is_Solution_def)
      apply (rule allI)
      by (simp add: f_PreFD_def)
    have unique_f3: "Solvable_unique 0 2 3 3 ?f3_f"
      apply (simp add: Solvable_unique_def)
      apply (rule allI, clarify, simp add: f_PreFD_def)
      apply (rule ex_ex1I)
      apply (rule_tac x = "\<lambda>na. 
        real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>0 na!(1)) 0\<rceil>)))" in exI)
      apply (simp)
      by (simp add: ext)
    have simp_1: "\<forall>x na. (\<lambda>x na. [if 1 \<le> x na!(0) * 2
              then (if na = 0 then 0
                    else min (vT_fd_sol_1
                               (\<lambda>n1. hd (f_PreFD
                                          (\<lambda>na. real_of_int
                                                 (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>))))
                                          0 x n1))
                               (\<lambda>n1. f_PreFD
                                      (\<lambda>na. real_of_int
                                             (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>))))
                                      0 x n1!(Suc 0))
                               (na - 1))
                          (hd (f_PreFD
                                (\<lambda>na. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>))))
                                0 x (na - 1)))) +
                   1
              else 0,
              real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))]) x na
      = (\<lambda>x na. [if 1 \<le> x na!(0) * 2
              then (if na = 0 then 0
                    else min (vT_fd_sol_1
                               (\<lambda>n1. (\<lambda>na. real_of_int
                                      (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) n1)
                               (\<lambda>n1. (x n1)!(0)) (na - 1))
                          ((\<lambda>na. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>))))
                                (na - 1))) + 1
              else 0,
              real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))]) x na"
      by (simp add: f_PreFD_def)
    let ?f4_f = "(\<lambda>x na. [if 1 \<le> x na!(0) * 2
              then (if na = 0 then 0
                    else min (vT_fd_sol_1
                               (\<lambda>n1. (\<lambda>na. real_of_int
                                      (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) n1)
                               (\<lambda>n1. (x n1)!(0)) (na - 1))
                          ((\<lambda>na. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>))))
                                (na - 1))) + 1
              else 0,
              real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))])"
    have f3_0: "(FBlock (\<lambda>x n. True) 3 3 ?f3_f) f\<^sub>D (0,2) 
        = (FBlock (\<lambda>x n. True) (3-1) (3-1)
            (\<lambda>x na. ((f_PostFD 2) 
            o ?f3_f
            o (f_PreFD (?f3_xx x) 0)) x na))"
      using is_solution_f3 unique_f3 simblock_f2 FBlock_feedback' by blast
    then have f3_1: "... = FBlock (\<lambda>x n. True) 2 2 ?f4_f"
      apply (simp (no_asm) add: f_PreFD_def f_PostFD_def)
      by (simp add: simp_1) 
    have simblock_f3_0: "SimBlock (3-1) (3-1) ((FBlock (\<lambda>x n. True) 3 3 ?f3_f) f\<^sub>D (0,2))"
      using simblock_f2 unique_f3 Solvable_unique_is_solvable SimBlock_FBlock_feedback by blast
    then have simblock_f3: "SimBlock 2 2 (FBlock (\<lambda>x n. True) 2 2 ?f4_f)"
      by (metis (no_types, lifting) One_nat_def Suc_1 diff_Suc_1 f3_0 f3_1 numeral_3_eq_3)
    (* variableTimer *)
    have simp_f4: "\<forall>x n. (f_RopGT \<circ> ?f4_f) x n = ?vt_f x n"
      using f_RopGT_def by simp
    have f4: "variableTimer = (FBlock (\<lambda>x n. True) 2 2 ?f4_f) ;; RopGT"
      using f3 f3_0 f3_1 variableTimer_def by auto
    then have f4_0: "... = FBlock (\<lambda>x n. True) 2 1 (f_RopGT \<circ> ?f4_f)"
      using simblock_f3 SimBlock_RopGT FBlock_seq_comp by (simp add: RopGT_def)
    then have f4_1: "... = FBlock (\<lambda>x n. True) 2 1 ?vt_f"
      using simp_f4 by presburger
    show ?thesis
      using f4 f4_0 f4_1 by auto
  qed

subsubsection  {* Verification \label{ssec:plf_vt_veri} *}
text {* @{text "vt_req_00"}: if $door\_open$ is false (door is closed), then the output of this 
subsystem is false. This is not a requirement described in the paper but we believe it should hold
 for this subsystem. *}

text {* Current Simulink diagram cannot guarantee this property because the type conversion int32 could
 cause its output less than 0 (i.e. 4294967295 = -10), finally the output of @{text "variableTimer"} 
could be true. It violates our requirement. In the original Simulink block diagram, this 
@{text "variableTimer"} is a subsystem of @{text "post_landing_finalize"} which itself is a subsystem
 of aircraft cabin pressure and environment control system applications. Therefore, its second input 
($door_open_time$) relies on the outputs of other subsystem (Timing Computation), and @{text "variableTimer"}
 actually makes assumptions on its input.

However, taking @{text "variableTimer"} alone, we try to verify this property either strengthen its 
precondition on the input ($door_open_times$ is always larger or equal to 0 and less than $2147483647/Rate$), 
or change int32 to uint32 for the type conversion block, or change the data type of this input t unsigned integer.

In the lemma below, we proved this property holds if we make an assumption on its values.
*}
lemma vt_req_00:
  " ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. (hd(x n) = 0 \<or> hd(x n) = 1) \<and> (* the first input door_open is boolean. *)
        (hd(tl(x n)) \<ge> 0 \<and> hd(tl(x n)) < 214748364))\<guillemotright> 
      (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred)
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>2\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>1\<guillemotright>) \<and>
      (head\<^sub>u(($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0) \<Rightarrow> (head\<^sub>u(($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0))
    )) \<sqsubseteq> variableTimer"
  apply (simp (no_asm) add: variableTimer_simp)
  apply (simp add: FBlock_def)
  apply (rel_simp)
  proof -
    fix ok\<^sub>v::"bool" and inouts\<^sub>v::"nat \<Rightarrow> real list" and ok\<^sub>v'::"bool" and inouts\<^sub>v' ::"nat \<Rightarrow> real list"
        and x :: nat
    assume a1: "\<forall>x. (hd (inouts\<^sub>v x) = 0 \<or> hd (inouts\<^sub>v x) = 1) \<and> 
        (0 \<le> hd (tl (inouts\<^sub>v x)) \<and> hd (tl (inouts\<^sub>v x)) < 214748364)"
    assume a2: "hd (inouts\<^sub>v x) = 0"
    assume a3: "\<forall>x. (x = 0 \<longrightarrow>
            (1 \<le> inouts\<^sub>v 0!(0) * 2 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
              length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [1] = inouts\<^sub>v' 0) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
              length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [0] = inouts\<^sub>v' 0)) \<and>
            (\<not> 1 \<le> inouts\<^sub>v 0!(0) * 2 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [1] = inouts\<^sub>v' 0) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [0] = inouts\<^sub>v' 0))) \<and>
           (0 < x \<longrightarrow>
            (1 \<le> inouts\<^sub>v x!(0) * 2 \<longrightarrow>
             (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
              < min (vT_fd_sol_1
                      (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                      (\<lambda>n1. inouts\<^sub>v n1!(0)) (x - Suc 0))
                 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                1 \<longrightarrow>
              length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [1] = inouts\<^sub>v' x) \<and>
             (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min (vT_fd_sol_1
                         (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                         (\<lambda>n1. inouts\<^sub>v n1!(0)) (x - Suc 0))
                    (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                   1 \<longrightarrow>
              length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [0] = inouts\<^sub>v' x)) \<and>
            (\<not> 1 \<le> inouts\<^sub>v x!(0) * 2 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [1] = inouts\<^sub>v' x) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [0] = inouts\<^sub>v' x)))"
    have 1: "\<forall>x. length(inouts\<^sub>v x) = 2"
        using a3 neq0_conv by blast
    have 2: "inouts\<^sub>v x!(0) = 0"
      using 1 a2 by (metis hd_conv_nth list.size(3) zero_not_eq_two)
    have 3: "\<forall>x. (0 \<le> inouts\<^sub>v x!(Suc 0) \<and> inouts\<^sub>v x!(Suc 0) < 214748364)"
      using a1 
      by (metis "1" One_nat_def diff_Suc_1 hd_conv_nth length_greater_0_conv length_tl 
        less_numeral_extra(1) nth_tl numeral_2_eq_2)
    have 30: "\<forall>x. Rate * max (inouts\<^sub>v x!(Suc 0)) 0 < Rate * 214748364 \<and> 
              Rate * max (inouts\<^sub>v x!(Suc 0)) 0 \<ge> 0"
      using 3 by simp
    have "\<forall>x. \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil> < (Rate * max (inouts\<^sub>v x!(Suc 0)) 0 + 1)"
      using ceiling_correct by linarith
    then have "\<forall>x. \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil> < (Rate * 214748364 + 1)"
      using 30 by (metis add.commute cancel_ab_semigroup_add_class.add_diff_cancel_left' 
        ceiling_less_iff less_eq_real_def numeral_times_numeral of_int_numeral one_plus_numeral)
    then have 31: "\<forall>x. \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil> < (Rate * 214748364 + 1) \<and> 
              \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil> \<ge> 0"
      using 30 by (smt ceiling_le_zero ceiling_zero)
    have 32: "\<forall>x. real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil> < (Rate * 214748364 + 1) \<and> 
              real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil> \<ge> 0"
      using 31 by (simp)
    have 33: "\<forall>x. RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>) 
                  = \<lfloor>real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>\<rfloor>"
      using RoundZero_def by (simp)
    have 34: "\<forall>x. RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>) < (Rate * 214748364 + 1) \<and> 
              RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>) \<ge> 0"
      using 33 31 by auto
    have 35: "\<forall>x. int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>))
        =  RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)"
      using 34 int32_eq by smt
    have 36: "\<forall>x. int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) 
                  < (Rate * 214748364 + 1) \<and> 
              int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) \<ge> 0"
      using 35 34 by (simp)
    show "hd (inouts\<^sub>v' x) = 0"
      using a2 a3 36 2
      by (metis (no_types, lifting) less_numeral_extra(1) list.sel(1) mult_zero_left neq0_conv not_le)
  qed

lemma door_open_time_range: 
  fixes x :: real and door_open_time::real
  assumes "door_open_time < 214748364 \<and> door_open_time > 0"
  assumes "(0 \<le> x \<and> x < door_open_time)"
  shows "int32 (RoundZero (real_of_int \<lceil>Rate * max x 0\<rceil>)) \<ge> 0 \<and> 
         int32 (RoundZero (real_of_int \<lceil>Rate * max x 0\<rceil>)) < (Rate * door_open_time + 1)"
  proof -
    have 0: "Rate * max x 0 < Rate * door_open_time \<and> Rate * max x 0 \<ge> 0"
      using assms by simp
    have 1: "\<lceil>Rate * max x 0\<rceil> < (Rate * max x 0 + 1)"
      using ceiling_correct by linarith
    then have "\<lceil>Rate * max x 0\<rceil> < (Rate * door_open_time + 1)"
      using 0 assms by linarith
    then have 2: "\<lceil>Rate * max x 0\<rceil> < (Rate * door_open_time + 1) \<and> 
              \<lceil>Rate * max x 0\<rceil> \<ge> 0"
      using 0 by (smt ceiling_le_zero ceiling_zero)
    have 3: "real_of_int \<lceil>Rate * max x 0\<rceil> < (Rate * door_open_time + 1) \<and> 
              real_of_int \<lceil>Rate * max x 0\<rceil> \<ge> 0"
      using 2 by (simp)
    have 4: "RoundZero (real_of_int \<lceil>Rate * max x 0\<rceil>) 
                  = \<lfloor>real_of_int \<lceil>Rate * max x 0\<rceil>\<rfloor>"
      using RoundZero_def by (simp)
    have 5: "RoundZero (real_of_int \<lceil>Rate * max x 0\<rceil>) < (Rate * door_open_time + 1) \<and> 
              RoundZero (real_of_int \<lceil>Rate * max x 0\<rceil>) \<ge> 0"
      using 3 4 by auto
    have 51: "RoundZero (real_of_int \<lceil>Rate * max x 0\<rceil>) < (Rate * 214748364 + 1) \<and> 
              RoundZero (real_of_int \<lceil>Rate * max x 0\<rceil>) \<ge> 0"
      using 5 assms by auto
    have 6: "int32 (RoundZero (real_of_int \<lceil>Rate * max x 0\<rceil>))
        =  RoundZero (real_of_int \<lceil>Rate * max x 0\<rceil>)"
      using 51 int32_eq assms by simp
    have 7: "int32 (RoundZero (real_of_int \<lceil>Rate * max x 0\<rceil>)) 
                  < (Rate * door_open_time + 1) \<and> 
              int32 (RoundZero (real_of_int \<lceil>Rate * max x 0\<rceil>)) \<ge> 0"
      using 5 6 by (simp)
    show ?thesis
      using 7 by blast
  qed

subsection {* Subsystem: @{text "rise1Shot"} \label{ssec:plf_rise1Shot}*}
text {* The @{text "rise1Shot"} subsystem is used for the purpose of making sure the finalize event 
 is only triggered by once if doors are continuously open. *}

definition "rise1Shot \<equiv> 
  (Split2 ;; (Id \<parallel>\<^sub>B (UnitDelay 1.0 (*3*);; LopNOT (*4*))) ;; LopAND 2 (*Rise_1*))"

text {* @{text "rise1Shot_simp_pat_f"} gives the function definition of the finally simplified 
subsystem. *}
abbreviation "rise1Shot_simp_pat_f \<equiv> (\<lambda>x n. [if (hd(x n) \<noteq> 0 \<and> (n > 0 \<and> hd(x (n-1)) = 0)) then 1 else 0])"

text {* @{text "rise1Shot_simp_pat"} is the simplified block for the subsystem. *}
abbreviation "rise1Shot_simp_pat \<equiv> (FBlock (\<lambda>x n. True) 1 1 rise1Shot_simp_pat_f)"

lemma SimBlock_rise1Shot_simp:
  "SimBlock 1 1 rise1Shot_simp_pat"
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [0]" in exI)
  apply (rule_tac x = "\<lambda>na. [0]" in exI)
  apply (simp)
  by simp

text {* @{text "rise1Shot_simp"} simplifies the subsystem into a block. *}
lemma rise1Shot_simp:
  "rise1Shot = rise1Shot_simp_pat"
  proof -
    (* (UnitDelay 1.0 (*3*);; LopNOT (*4*)) *)
    have f1: "(UnitDelay 1.0 (*3*);; LopNOT (*4*)) = FBlock (\<lambda>x n. True) 1 1 (f_LopNOT \<circ> f_UnitDelay 1)"
      using SimBlock_LopNOT SimBlock_UnitDelay by (simp add: FBlock_seq_comp f_sim_blocks)
    have simblock_f1: "SimBlock 1 1 (FBlock (\<lambda>x n. True) 1 1 (f_LopNOT \<circ> f_UnitDelay 1))"
      by (metis (no_types, lifting) LopNOT_def SimBlock_LopNOT SimBlock_FBlock_seq_comp 
          SimBlock_UnitDelay UnitDelay_def f1)
    (* (Id \<parallel>\<^sub>B (UnitDelay 1.0 (*3*);; LopNOT (*4*))) *)
    have f2: "(Id \<parallel>\<^sub>B (UnitDelay 1.0 (*3*);; LopNOT (*4*))) 
        = (Id \<parallel>\<^sub>B FBlock (\<lambda>x n. True) 1 1 (f_LopNOT \<circ> f_UnitDelay 1))"
      using f1 by (simp)
    then have f2_0: "... 
            = (FBlock (\<lambda>x n. True) 2 2 (\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                      (((f_LopNOT \<circ> f_UnitDelay 1) \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)))"
      using simblock_f1 SimBlock_Id FBlock_parallel_comp f1 
      proof -
        have "\<And>n na f. \<not> SimBlock n na (FBlock (\<lambda>f n. True) n na f) \<or> FBlock (\<lambda>f n. True) (n + 1) (na + 1) (\<lambda>fa na. (f \<circ> (\<lambda>f na. take n (f na))) fa na @ (f_LopNOT \<circ> f_UnitDelay 1 \<circ> (\<lambda>f na. drop n (f na))) fa na) = FBlock (\<lambda>f n. True) n na f \<parallel>\<^sub>B FBlock (\<lambda>f n. True) 1 1 (f_LopNOT \<circ> f_UnitDelay 1)"
          using FBlock_parallel_comp simblock_f1 by presburger
        then have "\<not> SimBlock 1 1 simu_contract_real.Id \<or> FBlock (\<lambda>f n. True) (1 + 1) (1 + 1) (\<lambda>f n. (f_Id \<circ> (\<lambda>f n. take 1 (f n))) f n @ (f_LopNOT \<circ> f_UnitDelay 1 \<circ> (\<lambda>f n. drop 1 (f n))) f n) = FBlock (\<lambda>f n. True) 1 1 f_Id \<parallel>\<^sub>B FBlock (\<lambda>f n. True) 1 1 (f_LopNOT \<circ> f_UnitDelay 1)"
          using simu_contract_real.Id_def by presburger
        then show ?thesis
          by (metis (no_types) SimBlock_Id Suc_1 Suc_eq_plus1 simu_contract_real.Id_def)
      qed
    have simblock_f2: "SimBlock 2 2 
          (FBlock (\<lambda>x n. True) 2 2 (\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                 (((f_LopNOT \<circ> f_UnitDelay 1) \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)))"
      by (metis (no_types, lifting) SimBlock_Id SimBlock_FBlock_parallel_comp Suc_1 Suc_eq_plus1 
          f2_0 simblock_f1 simu_contract_real.Id_def)
    (* Split2 ;; (Id \<parallel>\<^sub>B (UnitDelay 1.0 (*3*);; LopNOT (*4*))) *)
    have f3: "Split2 ;; (Id \<parallel>\<^sub>B (UnitDelay 1.0 (*3*);; LopNOT (*4*)))
          = Split2 ;; (FBlock (\<lambda>x n. True) 2 2 (\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                 (((f_LopNOT \<circ> f_UnitDelay 1) \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)))"
      using f2 f2_0 by (simp)
    then have f3_0: "... = (FBlock (\<lambda>x n. True) 1 2 
      ((\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                 (((f_LopNOT \<circ> f_UnitDelay 1) \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)) o f_Split2))"
      using SimBlock_Split2 simblock_f2 by (simp add: FBlock_seq_comp f_sim_blocks)
    have simblock_f3: "SimBlock 1 2 (FBlock (\<lambda>x n. True) 1 2 
      ((\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                 (((f_LopNOT \<circ> f_UnitDelay 1) \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)) o f_Split2))"
      by (smt SimBlock_FBlock_seq_comp SimBlock_Split2 Split2_def f3_0 simblock_f2)
    (* (Split2 ;; (Id \<parallel>\<^sub>B (UnitDelay 1.0 (*3*);; LopNOT (*4*))) ;; LopAND 2 (*Rise_1*)) *)
    have f4: "(Split2 ;; (Id \<parallel>\<^sub>B (UnitDelay 1.0 (*3*);; LopNOT (*4*))) ;; LopAND 2 (*Rise_1*))
      =  (FBlock (\<lambda>x n. True) 1 2 
      ((\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                 (((f_LopNOT \<circ> f_UnitDelay 1) \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)) o f_Split2))
         ;; LopAND 2 (*Rise_1*)"
      using f3 f3_0
      by (smt LopAND_def FBlock_seq_comp SimBlock_LopAND SimBlock_FBlock_seq_comp SimBlock_Split2 
          Split2_def comp_assoc f1 f2_0 neq0_conv simblock_f2 zero_not_eq_two)
    have f4_0: "... = (FBlock (\<lambda>x n. True) 1 1
      (f_LopAND o (\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                 (((f_LopNOT \<circ> f_UnitDelay 1) \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)) o f_Split2))"
      using SimBlock_LopAND simblock_f3 by (simp add: LopAND_def FBlock_seq_comp comp_assoc)
    have "\<forall>x n. (f_LopAND o (\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                 (((f_LopNOT \<circ> f_UnitDelay 1) \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)) o f_Split2) x n
      = ((\<lambda>x n. [if (hd(x n) \<noteq> 0 \<and> (n > 0 \<and> hd(x (n-1)) = 0)) then 1 else 0])) x n"
      using f_Id_def f_LopNOT_def f_UnitDelay_def f_LopAND_def f_Split2_def by simp
    then have "(f_LopAND o (\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                 (((f_LopNOT \<circ> f_UnitDelay 1) \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)) o f_Split2)
      = ((\<lambda>x n. [if (hd(x n) \<noteq> 0 \<and> (n > 0 \<and> hd(x (n-1)) = 0)) then 1 else 0]))"
      by blast
    then have f4_1: "(Split2 ;; (Id \<parallel>\<^sub>B (UnitDelay 1.0 (*3*);; LopNOT (*4*))) ;; LopAND 2 (*Rise_1*)) = 
        (FBlock (\<lambda>x n. True) 1 1 (\<lambda>x n. [if (hd(x n) \<noteq> 0 \<and> (n > 0 \<and> hd(x (n-1)) = 0)) then 1 else 0]))"
      using f4 f4_0 by (simp)
    then show ?thesis
      by (simp add: rise1Shot_def)
  qed

subsubsection {* Verification \label{ssec:plf_rise1shot_veri}*}
text {* @{text "rise1shot_req_00"} states that if the output of @{text "rise1Shot"} is true, then its
 present input must be true and the previous input must be false. In other word, the inputs that are 
continuously true won't trigger the output again.
*}

lemma rise1shot_req_00:
  " ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. (hd(x n) = 0 \<or> hd(x n) = 1))\<guillemotright> (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred)
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>1\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>1\<guillemotright>) \<and>
      (head\<^sub>u(($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<Rightarrow> 
        (\<guillemotleft>n\<guillemotright> >\<^sub>u 0 \<and> head\<^sub>u(($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1 \<and> head\<^sub>u(($inouts (\<guillemotleft>n-1\<guillemotright>)\<^sub>a)) =\<^sub>u 0))
    )) \<sqsubseteq> rise1Shot"
  apply (simp (no_asm) add: rise1Shot_simp)
  apply (simp add: FBlock_def)
  apply (rel_simp)
  by (metis list.sel(1) neq0_conv zero_neq_one)

subsection {* Subsystem: Latch \label{ssec:plf_latch}*}

text {* This subsystem implements a SR AND-OR latch and it has two inputs: 1st is S (set) and 2nd is 
R (reset) *}

text {* The first output is fed back into the first input. *}
(* A SR AND-OR latch: 
S   R   Action
0   0   No change
1   0   1
x   1   0
*)
definition "latch \<equiv> 
  ((((UnitDelay 0 (*3*) \<parallel>\<^sub>B Id) ;; (LopOR 2 (*1*)))  
    \<parallel>\<^sub>B 
    (Id ;; LopNOT (*2*))
   ) ;; (LopAND 2) (*Latch_1*) ;; Split2
  ) f\<^sub>D (0,0)"

(* calculate current output according to previous inputs *)
text {* @{text "latch_rec_calc_output"} is the solution for the feedback. *}
fun latch_rec_calc_output:: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
"latch_rec_calc_output S R 0 = 
    (if R 0 = 0 then (if S 0 = 0 then 0 else 1.0) else 0 )" |
"latch_rec_calc_output S R (Suc n) = 
    (if R (Suc n) = 0 then (if S (Suc n) = 0 then (latch_rec_calc_output S R (n)) else 1.0) else 0)"

lemma latch_rec_calc_output_0_1:
  "latch_rec_calc_output S R n = 0 \<or> latch_rec_calc_output S R n = 1"
  proof (induction n)
    case 0
    then show ?case by (simp)
  next
    case (Suc n)
    then show ?case by (simp)
  qed
 
(* is_Solution 0 0 3 2 
      ((\<lambda>x n. ([if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0,
               if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0]))) 
        (\<lambda>(inouts\<^sub>0::nat \<Rightarrow> real list). \<lambda>na. latch_rec_calc_output 
                        (\<lambda>n1. hd(inouts\<^sub>0 n1)) (\<lambda>n1. (inouts\<^sub>0 n1)!1) na)
*)
lemma latch_rec_calc_output_is_a_solution:
  fixes inouts\<^sub>0::"nat \<Rightarrow> real list" and n::nat
  assumes a1: "\<forall>x. length(inouts\<^sub>0 x) = 2"
  shows "((0 < n \<and> \<not> latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) 
            (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (n - Suc 0) = 0 \<or> \<not> hd (inouts\<^sub>0 n) = 0) \<and>
          inouts\<^sub>0 n!(Suc 0) = 0 \<longrightarrow>
              latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) n = 1) \<and>
       ((n = 0 \<or> latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) 
            (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (n - Suc 0) = 0) \<and> hd (inouts\<^sub>0 n) = 0 \<longrightarrow>
        latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) n = 0) \<and>
       (\<not> inouts\<^sub>0 n!(Suc 0) = 0 \<longrightarrow> latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) 
            (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) n = 0)"
  apply (rule conjI)
  apply (clarify)
  proof -
    assume a2: "0 < n \<and> \<not> latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (n - Suc 0) = 0 \<or>
      \<not> hd (inouts\<^sub>0 n) = 0"
    assume a3: "inouts\<^sub>0 n!(Suc 0) = 0"
    show "latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) n = 1"
    proof (cases)
      assume a4: "0 < n \<and> \<not> latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (n - Suc 0) = 0"
      from a4 have 1: "n > 0"
        by blast
      have 11: "latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) n =
            latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (Suc (n - Suc 0))"
        using 1 by simp
      show ?thesis
        proof (cases)
          assume a5: "hd (inouts\<^sub>0 n) = 0"
          from 11 have 12: "latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (Suc (n - Suc 0)) 
            = latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (n - Suc 0)"
            using a3 a5 apply (simp (no_asm))
            by (simp add: "1")
          show ?thesis
            using a4 latch_rec_calc_output_0_1 using "12" by auto
        next
          assume a5: "\<not>hd (inouts\<^sub>0 n) = 0"
          then have 12: "latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (Suc (n - Suc 0)) 
            = 1"
            using a3 a5 apply (simp (no_asm))
            by (simp add: "1")
          show ?thesis
            using a4 using "12" by auto
        qed
    next
      assume a4: "\<not> (0 < n \<and> \<not> latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (n - Suc 0) = 0)"
      then have 1: "\<not> hd (inouts\<^sub>0 n) = 0"
        using a2 by blast
      show ?thesis
        proof (cases)
          assume a5: "n = 0"
          show ?thesis
            using a5 apply (simp)
            using 1 a3 by blast
        next
          assume a5: "\<not>n = 0"
          then have a5': "n > 0"
            by simp
          have 11: "latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) n =
            latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (Suc (n - Suc 0))"
            using a5' by simp
          show ?thesis
            apply (simp only: "11")
            apply (simp)
            using 1 a3 by (simp add: a5')
        qed
    qed
  next
    show "((n = 0 \<or> latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) (n - Suc 0) = 0) \<and> hd (inouts\<^sub>0 n) = 0 \<longrightarrow>
        latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) n = 0) \<and>
       (\<not> inouts\<^sub>0 n!(Suc 0) = 0 \<longrightarrow> latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>0 n1)) (\<lambda>n1. inouts\<^sub>0 n1!(Suc 0)) n = 0)"
      proof (cases)
        assume a4: "n = 0"
        then show ?thesis 
          by simp
      next
        assume a4: "\<not> n = 0"
        then have a4': "n > 0" 
          by simp
        show ?thesis 
          apply (rule conjI, clarify)
          apply (metis Suc_pred a4 a4' latch_rec_calc_output.simps(2))
          using a4 a4' less_imp_Suc_add by fastforce
      qed
  qed

abbreviation "latch_simp_pat_f \<equiv> (\<lambda>x na. [if (0 < na \<and> 
                \<not> latch_rec_calc_output (\<lambda>n1. hd (x n1)) (\<lambda>n1. x n1!(Suc 0)) (na - Suc 0) = 0 
                \<or> \<not> hd (x na) = 0) \<and> x na!(Suc 0) = 0
              then 1 else 0])"

abbreviation "latch_simp_pat_f' \<equiv> (\<lambda>x na. [
                latch_rec_calc_output (\<lambda>n1. hd (x n1)) (\<lambda>n1. x n1!(Suc 0)) (na)])"

lemma latch_simp_pat_f_eq:
  "latch_simp_pat_f = latch_simp_pat_f'"
  proof -
    have 1: "\<forall>x na. latch_simp_pat_f x na = latch_simp_pat_f' x na"
      apply (rule allI)+
      apply (induct_tac na)
      proof -
        fix x na
        have 1: "[(if (0 < 0 \<and> \<not> latch_rec_calc_output (\<lambda>n1. hd (x n1)) (\<lambda>n1. x n1!(Suc 0)) (0 - Suc 0) = 0 \<or>
                     \<not> hd (x 0) = 0) \<and>
                    x 0!(Suc 0) = 0
                 then 1 else 0)] = [(if \<not> hd (x 0) = 0 \<and> x 0!(Suc 0) = 0 then 1 else 0)]"
          by (simp)
        have 2: "[latch_rec_calc_output (\<lambda>n1. hd (x n1)) (\<lambda>n1. x n1!(Suc 0)) 0] = 
                  [(if \<not> hd (x 0) = 0 \<and> x 0!(Suc 0) = 0 then 1 else 0)]"
          by (simp)
        show "[if (0 < 0 \<and> \<not> latch_rec_calc_output (\<lambda>n1. hd (x n1)) (\<lambda>n1. x n1!(Suc 0)) (0 - Suc 0) = 0 \<or>
                     \<not> hd (x 0) = 0) \<and>
                    x 0!(Suc 0) = 0
                 then 1 else 0] =
                [latch_rec_calc_output (\<lambda>n1. hd (x n1)) (\<lambda>n1. x n1!(Suc 0)) 0]"
          using 1 2 by (simp)
      next
        fix x na n
        assume a1: "[if (0 < n \<and> 
          \<not> latch_rec_calc_output (\<lambda>n1. hd (x n1)) (\<lambda>n1. x n1!(Suc 0)) (n - Suc 0) = 0 \<or> 
              \<not> hd (x n) = 0) \<and> x n!(Suc 0) = 0
            then 1 else 0] =
           [latch_rec_calc_output (\<lambda>n1. hd (x n1)) (\<lambda>n1. x n1!(Suc 0)) n]"
        show "[if (0 < Suc n \<and> \<not> latch_rec_calc_output (\<lambda>n1. hd (x n1)) (\<lambda>n1. x n1!(Suc 0)) (Suc n - Suc 0) = 0 \<or>
                \<not> hd (x (Suc n)) = 0) \<and>
               x (Suc n)!(Suc 0) = 0
            then 1 else 0] =
           [latch_rec_calc_output (\<lambda>n1. hd (x n1)) (\<lambda>n1. x n1!(Suc 0)) (Suc n)]"
          using a1 latch_rec_calc_output_0_1 by force
      qed
    show ?thesis
      using 1 by simp
  qed
    
abbreviation "latch_simp_pat \<equiv> FBlock (\<lambda>x n. True) 2 1 latch_simp_pat_f"

lemma SimBlock_latch_simp: 
   "SimBlock 2 1 latch_simp_pat"
  apply (rule SimBlock_FBlock)
  apply (rule_tac x = "\<lambda>na. [0, 1]" in exI)
  apply (rule_tac x = "\<lambda>na. [0]" in exI)
  apply (simp)
  by simp

abbreviation "latch_simp_pat' \<equiv> FBlock (\<lambda>x n. True) 2 1 latch_simp_pat_f'"

lemma SimBlock_latch_simp': 
   "SimBlock 2 1 latch_simp_pat'"
  using SimBlock_latch_simp latch_simp_pat_f_eq
  by simp

lemma latch_simp: 
  "latch = latch_simp_pat'"
  proof -
    (* (UnitDelay 0 (*3*) \<parallel>\<^sub>B Id) *)
    have f1: "(UnitDelay 0 (*3*) \<parallel>\<^sub>B Id) = (FBlock (\<lambda>x n. True) (2) (2) 
        (\<lambda>x n. [if n = 0 then 0 else hd(x (n-1)), hd(tl(x n))]))"
      using UnitDelay_Id_parallel_comp by (simp)
    have simblock_f1: "SimBlock 2 2 (FBlock (\<lambda>x n. True) (2) (2) 
        (\<lambda>x n. [if n = 0 then 0 else hd(x (n-1)), hd(tl(x n))]))"
      by (metis (no_types, lifting) SimBlock_Id SimBlock_FBlock_parallel_comp SimBlock_UnitDelay 
        Suc_1 Suc_eq_plus1 UnitDelay_Id_parallel_comp UnitDelay_def Id_def)
    (* ((UnitDelay 0 (*3*) \<parallel>\<^sub>B Id) ;; (LopOR 2 (*1*))) *)
    have f2: "((UnitDelay 0 (*3*) \<parallel>\<^sub>B Id) ;; (LopOR 2 (*1*))) = (FBlock (\<lambda>x n. True) (2) (2) 
        (\<lambda>x n. [if n = 0 then 0 else hd(x (n-1)), hd(tl(x n))])) ;; (LopOR 2 (*1*))"
      by (simp add: UnitDelay_Id_parallel_comp)
    have f2_0: "... = FBlock (\<lambda>x n. True) (2) (1) 
      (f_LopOR o (\<lambda>x n. [if n = 0 then 0 else hd(x (n-1)), hd(tl(x n))]))"
      using LopOR_def FBlock_seq_comp SimBlock_LopOR simblock_f1 by auto
    have f2_1: "... = FBlock (\<lambda>x n. True) (2) (1) 
      (\<lambda>x n. [if (n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0 then 1::real else 0])"
      proof -
        have "\<forall>x n. ((f_LopOR o (\<lambda>x n. [if n = 0 then 0 else hd(x (n-1)), hd(tl(x n))])) x n 
          = (\<lambda>x n. [if (n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0 then 1::real else 0]) x n)"
          using f_LopOR_def by auto
        then show ?thesis
          by presburger
      qed
    have simblock_f2: "SimBlock 2 1 (FBlock (\<lambda>x n. True) (2) (1) 
      (\<lambda>x n. [if (n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0 then 1::real else 0]))"
      by (metis (no_types, lifting) LopOR_def SimBlock_LopOR SimBlock_FBlock_seq_comp f2_0 f2_1 
          pos2 simblock_f1)
    (* (Id ;; LopNOT (*2*)) *)
    have f3: "(Id ;; LopNOT (*2*)) = (FBlock (\<lambda>x n. True) (1) (1) (f_LopNOT o f_Id))"
      by (metis LopNOT_def One_nat_def FBlock_seq_comp SimBlock_Id SimBlock_LopNOT 
          simu_contract_real.Id_def)
    then have f3_0: "... = (FBlock (\<lambda>x n. True) (1) (1) 
        (\<lambda>x n. [if hd(x n) = 0 then 1 else 0]))"
      proof -
        have "\<forall>x n. ((f_LopNOT o f_Id) x n = (\<lambda>x n. [if hd(x n) = 0 then 1 else 0]) x n)"
          by (simp add: f_Id_def f_LopNOT_def)
        then show ?thesis
          by presburger
      qed
    have simblock_f3: "SimBlock 1 1 (FBlock (\<lambda>x n. True) (1) (1) 
        (\<lambda>x n. [if hd(x n) = 0 then 1 else 0]))"
      by (metis LopNOT_def SimBlock_Id SimBlock_LopNOT SimBlock_FBlock_seq_comp f3 f3_0 Id_def)
    (* (((UnitDelay 0 (*3*) \<parallel>\<^sub>B Id) ;; (LopOR 2 (*1*)))  
        \<parallel>\<^sub>B 
        (Id ;; LopNOT (*2*))
       )
    *)
    let ?P = "(\<lambda>x n. [if (n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0 then 1::real else 0])"
    let ?Q = "(\<lambda>x n. [if hd(x n) = 0 then 1 else 0])"
    have f4: "(((UnitDelay 0 (*3*) \<parallel>\<^sub>B Id) ;; (LopOR 2 (*1*))) \<parallel>\<^sub>B (Id ;; LopNOT (*2*))) 
      = (FBlock (\<lambda>x n. True) (2) (1) ?P) \<parallel>\<^sub>B  (FBlock (\<lambda>x n. True) (1) (1) ?Q)"
      using f2 f2_0 f2_1 f3 f3_0 by auto
    then have f4_0: "... = FBlock (\<lambda>x n. True) (2+1) (1+1) 
      (\<lambda>x n. (((?P \<circ> (\<lambda>xx nn. take 2 (xx nn))) x n) 
             @ ((?Q \<circ> (\<lambda>xx nn. drop 2 (xx nn)))) x n))"
      using SimBlock_UnitDelay SimBlock_Id SimBlock_LopOR SimBlock_LopNOT simblock_f1 simblock_f2 simblock_f3 
        by (simp add: FBlock_parallel_comp f_sim_blocks)
    then have f4_1: "... = FBlock (\<lambda>x n. True) 3 2 
      (\<lambda>x n. (((?P \<circ> (\<lambda>xx nn. take 2 (xx nn))) x n) 
             @ ((?Q \<circ> (\<lambda>xx nn. drop 2 (xx nn)))) x n))"
      using Suc_eq_plus1 nat_1_add_1 numeral_2_eq_2 numeral_3_eq_3 by presburger
    have f4_2: "FBlock (\<lambda>x n. True) 3 2 
        (\<lambda>x n. (((?P \<circ> (\<lambda>xx nn. take 2 (xx nn))) x n) 
             @ ((?Q \<circ> (\<lambda>xx nn. drop 2 (xx nn)))) x n)) 
      = FBlock (\<lambda>x n. True) 3 2 
        (\<lambda>x n. ([if (n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0 then 1::real else 0, 
                if (x n)!2 = 0 then 1 else 0]))"
      proof -
        have 1: "\<forall>(x::nat \<Rightarrow> real list) n::nat. length(x n) > 2 \<longrightarrow> 
          (((?Q \<circ> (\<lambda>xx nn. drop 2 (xx nn)))) x n
          = (\<lambda>x n. [if (x n)!2 = 0 then 1 else 0]) x n)"
          apply (auto)
          apply (simp add: hd_drop_conv_nth)
          by (simp add: hd_drop_conv_nth)
        have 2: "\<forall>(x::nat \<Rightarrow> real list) n::nat. ((\<lambda>x n. (((?P \<circ> (\<lambda>xx nn. take 2 (xx nn))) x n) 
                    @ ((?Q \<circ> (\<lambda>xx nn. drop 2 (xx nn)))) x n)) x n 
            =  (\<lambda>x n. (((\<lambda>x n. [if (n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0 then 1::real else 0]) x n) 
             @ ((?Q \<circ> (\<lambda>xx nn. drop 2 (xx nn)))) x n)) x n)"
          apply (auto)
          apply (metis append_take_drop_id hd_append2 take_eq_Nil zero_not_eq_two)
          apply (metis Suc_1 append_take_drop_id hd_append2 take_eq_Nil take_tl zero_neq_one)
          apply (metis Suc_1 append_take_drop_id hd_append2 take_eq_Nil take_tl zero_neq_one)
          apply (metis Suc_1 hd_conv_nth less_numeral_extra(1) nth_take take_eq_Nil take_tl zero_neq_one)
          apply (metis Suc_1 append_take_drop_id hd_append2 take_eq_Nil take_tl zero_neq_one)
          apply (metis append_take_drop_id hd_append2 take_eq_Nil zero_not_eq_two)
          by (metis Suc_1 append_take_drop_id hd_append2 take_eq_Nil take_tl zero_neq_one)
        have 3: "\<forall>(x::nat \<Rightarrow> real list) n::nat. length(x n) > 2 \<longrightarrow>
            ((\<lambda>x n. (((\<lambda>x n. [if (n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0 then 1::real else 0]) x n) 
             @ ((?Q \<circ> (\<lambda>xx nn. drop 2 (xx nn)))) x n)) x n 
            =  (\<lambda>x n. ([if (n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0 then 1::real else 0, 
                if (x n)!2 = 0 then 1 else 0])) x n)"
          using hd_drop_m by simp
        have 4: "\<forall>(x::nat \<Rightarrow> real list) n::nat. length(x n) > 2 \<longrightarrow> 
              ((\<lambda>x n. (((?P \<circ> (\<lambda>xx nn. take 2 (xx nn))) x n) 
                    @ ((?Q \<circ> (\<lambda>xx nn. drop 2 (xx nn)))) x n)) x n
                = (\<lambda>x n. ([if (n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0 then 1::real else 0, 
                if (x n)!2 = 0 then 1 else 0])) x n)"
          using 1 2 by simp
        show ?thesis
          apply (simp add: FBlock_def)
          apply (rel_simp)
          apply (rule iffI)
          apply (clarify)
          defer
          apply (clarify)
          defer
          proof -
            fix ok\<^sub>v inouts\<^sub>v::"nat \<Rightarrow> real list" and  ok\<^sub>v' inouts\<^sub>v'::"nat \<Rightarrow> real list" and x::nat
            assume a1: "\<forall>x. (hd (drop 2 (inouts\<^sub>v x)) = 0 \<longrightarrow>
              (0 < x \<and> \<not> hd (take 2 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
              (\<not> hd (tl (take 2 (inouts\<^sub>v x))) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
              ((x = 0 \<or> hd (take 2 (inouts\<^sub>v (x - Suc 0))) = 0) \<and> hd (tl (take 2 (inouts\<^sub>v x))) = 0 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> hd (drop 2 (inouts\<^sub>v x)) = 0 \<longrightarrow>
              (0 < x \<and> \<not> hd (take 2 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 0] = inouts\<^sub>v' x) \<and>
              (\<not> hd (tl (take 2 (inouts\<^sub>v x))) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 0] = inouts\<^sub>v' x) \<and>
              ((x = 0 \<or> hd (take 2 (inouts\<^sub>v (x - Suc 0))) = 0) \<and> hd (tl (take 2 (inouts\<^sub>v x))) = 0 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))"
            from a1 have len_3: "\<forall>na. length(inouts\<^sub>v na) = 3"
              by (meson neq0_conv)
            from len_3 have hd_drop: "(hd (drop 2 (inouts\<^sub>v x)) = inouts\<^sub>v x!(2))"
              by (simp add: hd_drop_conv_nth)
            have hd_take: "hd (take 2 (inouts\<^sub>v (x - Suc 0))) = hd (inouts\<^sub>v (x - Suc 0))"
              by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
            have hd_tl_take: "hd (tl (take 2 (inouts\<^sub>v x))) = hd (tl (inouts\<^sub>v x))"
              by (metis Suc_1 hd_conv_nth less_numeral_extra(1) nth_take take_eq_Nil take_tl zero_neq_one)
            show "(inouts\<^sub>v x!(2) = 0 \<longrightarrow>
              (0 < x \<and> \<not> hd (inouts\<^sub>v (x - Suc 0)) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
              (\<not> hd (tl (inouts\<^sub>v x)) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
              ((x = 0 \<or> hd (inouts\<^sub>v (x - Suc 0)) = 0) \<and> hd (tl (inouts\<^sub>v x)) = 0 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> inouts\<^sub>v x!(2) = 0 \<longrightarrow>
              (0 < x \<and> \<not> hd (inouts\<^sub>v (x - Suc 0)) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 0] = inouts\<^sub>v' x) \<and>
              (\<not> hd (tl (inouts\<^sub>v x)) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 0] = inouts\<^sub>v' x) \<and>
              ((x = 0 \<or> hd (inouts\<^sub>v (x - Suc 0)) = 0) \<and> hd (tl (inouts\<^sub>v x)) = 0 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))"
              using a1 hd_drop hd_take hd_tl_take by presburger
          next
            fix ok\<^sub>v::bool and inouts\<^sub>v::"nat \<Rightarrow> real list" and  ok\<^sub>v'::bool and inouts\<^sub>v'::"nat \<Rightarrow> real list" and x::nat
            assume a1: "(\<forall>x. (inouts\<^sub>v x!(2) = 0 \<longrightarrow>
                     (0 < x \<and> \<not> hd (inouts\<^sub>v (x - Suc 0)) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                     (\<not> hd (tl (inouts\<^sub>v x)) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                     ((x = 0 \<or> hd (inouts\<^sub>v (x - Suc 0)) = 0) \<and> hd (tl (inouts\<^sub>v x)) = 0 \<longrightarrow>
                      length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 1] = inouts\<^sub>v' x)) \<and>
                    (\<not> inouts\<^sub>v x!(2) = 0 \<longrightarrow>
                     (0 < x \<and> \<not> hd (inouts\<^sub>v (x - Suc 0)) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 0] = inouts\<^sub>v' x) \<and>
                     (\<not> hd (tl (inouts\<^sub>v x)) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 0] = inouts\<^sub>v' x) \<and>
                     ((x = 0 \<or> hd (inouts\<^sub>v (x - Suc 0)) = 0) \<and> hd (tl (inouts\<^sub>v x)) = 0 \<longrightarrow>
                      length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)))"
            from a1 have len_3: "\<forall>na. length(inouts\<^sub>v na) = 3"
              by (meson neq0_conv)
            from len_3 have hd_drop: "(hd (drop 2 (inouts\<^sub>v x)) = inouts\<^sub>v x!(2))"
              by (simp add: hd_drop_conv_nth)
            have hd_take: "hd (take 2 (inouts\<^sub>v (x - Suc 0))) = hd (inouts\<^sub>v (x - Suc 0))"
              by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
            have hd_tl_take: "hd (tl (take 2 (inouts\<^sub>v x))) = hd (tl (inouts\<^sub>v x))"
              by (metis Suc_1 hd_conv_nth less_numeral_extra(1) nth_take take_eq_Nil take_tl zero_neq_one)
            show "((hd (drop 2 (inouts\<^sub>v x)) = 0 \<longrightarrow>
                     (0 < x \<and> \<not> hd (take 2 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                     (\<not> hd (tl (take 2 (inouts\<^sub>v x))) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                     ((x = 0 \<or> hd (take 2 (inouts\<^sub>v (x - Suc 0))) = 0) \<and> hd (tl (take 2 (inouts\<^sub>v x))) = 0 \<longrightarrow>
                      length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 1] = inouts\<^sub>v' x)) \<and>
                    (\<not> hd (drop 2 (inouts\<^sub>v x)) = 0 \<longrightarrow>
                     (0 < x \<and> \<not> hd (take 2 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 0] = inouts\<^sub>v' x) \<and>
                     (\<not> hd (tl (take 2 (inouts\<^sub>v x))) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 0] = inouts\<^sub>v' x) \<and>
                     ((x = 0 \<or> hd (take 2 (inouts\<^sub>v (x - Suc 0))) = 0) \<and> hd (tl (take 2 (inouts\<^sub>v x))) = 0 \<longrightarrow>
                      length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)))"
              by (simp add: a1 hd_drop hd_take hd_tl_take)
          qed
      qed
    then have f4_3: "(((UnitDelay 0 (*3*) \<parallel>\<^sub>B Id) ;; (LopOR 2 (*1*))) \<parallel>\<^sub>B (Id ;; LopNOT (*2*)))
           = FBlock (\<lambda>x n. True) 3 2 
        (\<lambda>x n. ([if (n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0 then 1::real else 0, 
                if (x n)!2 = 0 then 1 else 0]))"
      using f4 f4_0 f4_1 by simp
    have simblock_f4: "SimBlock 3 2 (FBlock (\<lambda>x n. True) 3 2 
        (\<lambda>x n. ([if (n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0 then 1::real else 0, 
                if (x n)!2 = 0 then 1 else 0])))"
      by (metis (no_types, lifting) One_nat_def SimBlock_FBlock_parallel_comp Suc_1 Suc_eq_plus1 f4 
        f4_3 numeral_3_eq_3 simblock_f2 simblock_f3)
    (* ((((UnitDelay 0 (*3*) \<parallel>\<^sub>B Id) ;; (LopOR 2 (*1*)))  
        \<parallel>\<^sub>B 
        (Id ;; LopNOT (*2*))
       ) ;; (LopAND 2) (*Latch_1*) *)
    have f5: "((((UnitDelay 0 (*3*) \<parallel>\<^sub>B Id) ;; (LopOR 2 (*1*)))  
              \<parallel>\<^sub>B 
              (Id ;; LopNOT (*2*))
             ) ;; (LopAND 2) (*Latch_1*)) =
      FBlock (\<lambda>x n. True) 3 2 
        (\<lambda>x n. ([if (n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0 then 1::real else 0, 
                if (x n)!2 = 0 then 1 else 0])) ;; (LopAND 2)"
      using f4_3 by simp
    then have f5_0: "... = FBlock (\<lambda>x n. True) 3 1
        (f_LopAND o (\<lambda>x n. ([if (n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0 then 1::real else 0, 
                if (x n)!2 = 0 then 1 else 0])))"
      by (metis (no_types, lifting) LopAND_def One_nat_def FBlock_seq_comp SimBlock_LopAND 
            SimBlock_FBlock_parallel_comp Suc_1 Suc_eq_plus1 f4 f4_3 numeral_3_eq_3 pos2 simblock_f2 simblock_f3)
    then have f5_1: "... = FBlock (\<lambda>x n. True) 3 1
        (\<lambda>x n. ([if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0]))"
      proof -
        have "\<forall>x n. (f_LopAND o (\<lambda>x n. ([if (n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0 then 1::real else 0, 
                if (x n)!2 = 0 then 1 else 0]))) x n
          = (\<lambda>x n. ([if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0])) x n"
          by (simp add: f_LopAND_def)
        then show ?thesis
          apply (simp add: FBlock_def)
          apply (rel_simp)
          apply (simp add: f_LopAND_def)
          apply (rule iffI)
          apply (clarify)
          using neq0_conv apply blast
          apply (clarify)
          by blast
      qed
    have simblock_f5: "SimBlock 3 1 (FBlock (\<lambda>x n. True) 3 1
        (\<lambda>x n. ([if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0])))"
      using simblock_f4
      by (metis (no_types, lifting) LopAND_def SimBlock_LopAND SimBlock_FBlock_seq_comp f5_0 f5_1 pos2)
    (* ((((UnitDelay 0 (*3*) \<parallel>\<^sub>B Id) ;; (LopOR 2 (*1*)))  
        \<parallel>\<^sub>B 
        (Id ;; LopNOT (*2*))
       ) ;; (LopAND 2) (*Latch_1*) ;; Split2 *)
    have f6: "((((UnitDelay 0 (*3*) \<parallel>\<^sub>B Id) ;; (LopOR 2 (*1*)))  
              \<parallel>\<^sub>B 
              (Id ;; LopNOT (*2*))) ;; (LopAND 2) (*Latch_1*) ;; Split2)
      = (FBlock (\<lambda>x n. True) 3 1
        (\<lambda>x n. ([if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0]))
        ;; Split2)"
      using f5 f5_0 f5_1 by (simp add: RA1)
    then have f6_0: "... = (FBlock (\<lambda>x n. True) 3 2 (f_Split2 o 
      (\<lambda>x n. ([if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0]))))"
      using Split2_def FBlock_seq_comp simblock_f5 by (metis (no_types, lifting) SimBlock_Split2)
    then have f6_1: "... = (FBlock (\<lambda>x n. True) 3 2 
      ((\<lambda>x n. ([if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0,
        if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0]))))"
      proof -
      have "\<forall>n f. [if (0 < n \<and> \<not> hd (f (n - 1)) = (0::real) \<or> \<not> hd (tl (f n)) = 0) \<and> 
          f n!(2) = (0::real) then 1 else 0, if (0 < n \<and> \<not> hd (f (n - 1)) = 0 \<or> 
          \<not> hd (tl (f n)) = 0) \<and> f n!(2) = (0::real) then 1 else 0] = 
        (f_Split2 \<circ> (\<lambda>f n. [if (0 < n \<and> \<not> hd (f (n - 1)) = 0 \<or> \<not> hd (tl (f n)) = 0) \<and> 
          f n!(2) = (0::real) then 1 else 0])) f n"
        by (simp add: f_Split2_def)
        then show ?thesis
          by presburger
      qed
    have simblock_f6: "SimBlock 3 2 (FBlock (\<lambda>x n. True) 3 2 
      ((\<lambda>x n. ([if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0,
        if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0]))))"
      using simblock_f5 SimBlock_Split2
      by (smt SimBlock_FBlock_seq_comp Split2_def f6_0 f6_1)
    let ?f6 = "(FBlock (\<lambda>x n. True) 3 2 
      ((\<lambda>x n. ([if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0,
        if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0]))))"
    have inps_f6: "inps ?f6 = 3"
      using inps_P simblock_f6 by blast
    have outps_f6: "outps ?f6 = 2"
      using outps_P simblock_f6 by blast
    (* latch *)
    have f7: "latch = ?f6 f\<^sub>D (0,0)"
      using f6 f6_0 f6_1 latch_def by simp
    have is_solution_f7: "is_Solution 0 0 3 2 
      ((\<lambda>x n. ([if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0,
               if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0]))) 
        (\<lambda>(inouts\<^sub>0::nat \<Rightarrow> real list). \<lambda>na. latch_rec_calc_output 
                        (\<lambda>n1. hd(inouts\<^sub>0 n1)) (\<lambda>n1. (inouts\<^sub>0 n1)!1) na)"
      apply (simp add: is_Solution_def)
      apply (rule allI)
      apply (clarify)
      apply (simp add: f_PreFD_def)
      using latch_rec_calc_output_is_a_solution by blast
    have unique_f7: "Solvable_unique 0 0 3 2 
      (\<lambda>x n. ([if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0,
               if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0]))"
      apply (simp add: Solvable_unique_def)
      apply (rule allI, clarify, simp add: f_PreFD_def)
      apply (rule ex_ex1I)
      apply (rule_tac x = "\<lambda>na. latch_rec_calc_output (\<lambda>n1. hd(inouts\<^sub>0 n1)) (\<lambda>n1. (inouts\<^sub>0 n1)!1) na" in exI)
      apply (simp)
      apply (rule allI)
      using latch_rec_calc_output_is_a_solution apply blast
      proof -
        fix inouts\<^sub>0::"nat \<Rightarrow> real list" and xx y ::"nat \<Rightarrow> real"
        assume a1: "\<forall>n. ((0 < n \<and> \<not> xx (n - Suc 0) = 0 \<or> \<not> hd (inouts\<^sub>0 n) = 0) \<and> 
                          inouts\<^sub>0 n!(Suc 0) = 0 \<longrightarrow> xx n = 1) \<and>
                        ((n = 0 \<or> xx (n - Suc 0) = 0) \<and> hd (inouts\<^sub>0 n) = 0 \<longrightarrow> xx n = 0) \<and> 
                          (\<not> inouts\<^sub>0 n!(Suc 0) = 0 \<longrightarrow> xx n = 0)"
        assume a2: "\<forall>n. ((0 < n \<and> \<not> y (n - Suc 0) = 0 \<or> \<not> hd (inouts\<^sub>0 n) = 0) \<and> 
                          inouts\<^sub>0 n!(Suc 0) = 0 \<longrightarrow> y n = 1) \<and>
                        ((n = 0 \<or> y (n - Suc 0) = 0) \<and> hd (inouts\<^sub>0 n) = 0 \<longrightarrow> y n = 0) \<and> 
                          (\<not> inouts\<^sub>0 n!(Suc 0) = 0 \<longrightarrow> y n = 0)"
        have 1: "\<forall>n. xx n = y n"
          apply (rule allI)
          proof -
            fix n::nat
            show "xx n = y n"
              proof (induct n)
                case 0
                then show ?case 
                  using a1 a2 by metis
              next
                case (Suc n) note IH = this
                then show ?case
                  using a1 a2 by (metis One_nat_def diff_Suc_1 zero_less_Suc)
              qed
          qed
        show "xx = y"
          using 1 fun_eq by (blast)
      qed
    have f7_0: 
      "?f6 f\<^sub>D (0,0) = (FBlock (\<lambda>x n. True) (3-1) (2-1)
            (\<lambda>x na. ((f_PostFD 0) 
            o (\<lambda>x n. ([if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0,
                if ((n > 0 \<and> hd(x (n-1)) \<noteq> 0) \<or> hd(tl(x n)) \<noteq> 0) \<and> (x n)!2 = 0 then 1::real else 0])) 
            o (f_PreFD ((\<lambda>(inouts\<^sub>0::nat \<Rightarrow> real list). \<lambda>na. latch_rec_calc_output 
                        (\<lambda>n1. hd(inouts\<^sub>0 n1)) (\<lambda>n1. (inouts\<^sub>0 n1)!1) na) x) 0)) x na))"
      using FBlock_feedback' f7 is_solution_f7 unique_f7 simblock_f6 by blast
    then have f7_1: "... = FBlock (\<lambda>x n. True) 2 1 
      (\<lambda>x na. [if (0 < na \<and> 
                \<not> latch_rec_calc_output (\<lambda>n1. hd (x n1)) (\<lambda>n1. x n1!(Suc 0)) (na - Suc 0) = 0 
                \<or> \<not> hd (x na) = 0) \<and> x na!(Suc 0) = 0
              then 1 else 0])"
      by (simp (no_asm) add: f_PreFD_def f_PostFD_def)
    show ?thesis
      using f7 f7_0 f7_1 latch_simp_pat_f_eq by (simp)
  qed

subsubsection {* Verification \label{ssec:plf_latch_veri}*}
(* A SR AND-OR latch: 
S   R   Action
0   0   No change
1   0   1
x   1   0
*)
text {* @{text "latch_req_00"}: if R is true, then the output is always false. *}
lemma latch_req_00:
  " ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. ((hd(x n) = 0 \<or> hd(x n) = 1) \<and> (hd(tl(x n)) = 0 \<or> hd(tl(x n)) = 1)))\<guillemotright> 
        (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred) 
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>2\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>1\<guillemotright>) \<and>
      (head\<^sub>u(tail\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) \<noteq>\<^sub>u 0) \<Rightarrow> (head\<^sub>u(($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0))
    )) \<sqsubseteq> latch"
  using latch_simp apply (simp add: latch_def)
  proof -
    show "(\<^bold>\<forall> n \<bullet> \<guillemotleft>\<lambda>x n. (hd (x n) = 0 \<or> hd (x n) = 1) \<and> (hd (tl (x n)) = 0 \<or> hd (tl (x n)) = 1)\<guillemotright>
      (&inouts)\<^sub>a(\<guillemotleft>n\<guillemotright>)\<^sub>a) \<turnstile>\<^sub>n
      (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>2\<guillemotright> \<and>
            #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>Suc 0\<guillemotright> \<and> head\<^sub>u(tail\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a)) \<noteq>\<^sub>u 0 \<Rightarrow>
            head\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u 0) 
      \<sqsubseteq>
      FBlock (\<lambda>x n. True) 2 (Suc 0)
       (\<lambda>x na. [latch_rec_calc_output (\<lambda>n1. hd (x n1)) (\<lambda>n1. x n1!(Suc 0)) na])"
      apply (simp add: FBlock_def)
      apply (rule ndesign_refine_intro)
      apply simp
      apply (rel_simp)
      proof -
        fix inouts\<^sub>v inouts\<^sub>v'::"nat \<Rightarrow> real list" and x::nat
        assume a1: "\<forall>x. (hd (inouts\<^sub>v x) = 0 \<or> hd (inouts\<^sub>v x) = 1) \<and> (hd (tl (inouts\<^sub>v x)) = 0 \<or> 
                    hd (tl (inouts\<^sub>v x)) = 1)"
        assume a2: "\<forall>x. length(inouts\<^sub>v x) = 2 \<and>
           length(inouts\<^sub>v' x) = Suc 0 \<and>
           [latch_rec_calc_output (\<lambda>n1. hd (inouts\<^sub>v n1)) (\<lambda>n1. inouts\<^sub>v n1!(Suc 0)) x] = inouts\<^sub>v' x"
        assume a3: "\<not> hd (tl (inouts\<^sub>v x)) = 0"
        have 1: "\<not> inouts\<^sub>v x!(Suc 0) = 0"
          using a2 a3
          by (metis One_nat_def Suc_1 diff_Suc_1 diff_is_0_eq hd_conv_nth length_tl 
            less_numeral_extra(1) list.size(3) not_one_le_zero nth_tl)
        have 2: "inouts\<^sub>v' x = [0]"
          using a2 1 
          by (metis (mono_tags, lifting) latch_rec_calc_output.elims)
        then show "hd (inouts\<^sub>v' x) = 0"
          by (simp)
    qed
  qed

subsection {* System: @{text "post_landing_finalize"} *}

text {* @{text "post_mode"} is a part of block compositions from the input $mode$ to the three-way AND logic 
block. *}
(* from aircraft mode to and1 *)
(* 
  input: mode: in1, uint32, 1/10s
  output: (and1\<longrightarrow>and3)
*)
definition "post_mode \<equiv> 
  (Split2 (* mode is split into two *) ;; 
    (
      ((UnitDelay 0 (*IC = 0, r=1/10s*) \<parallel>\<^sub>B Const 4 (*landing, uint32(4), r=1/10s*)) ;; RopEQ)
      \<parallel>\<^sub>B
      ((Id \<parallel>\<^sub>B Const 8 (*ground, uint32(8), r=1/10s*)) ;; RopEQ)
    )
  )
"

lemma post_mode_simp:
  "post_mode = (FBlock (\<lambda>x n. True) (1) (2)
      (\<lambda>x n. (([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0, if hd(x n) = 8 then 1 else 0]))))"
  proof -
    (* (UnitDelay 0 (*IC = 0, r=1/10s*) \<parallel>\<^sub>B Const 4 (*landing, uint32(4), r=1/10s*)) *)
    have f1: "(UnitDelay 0 (*IC = 0, r=1/10s*) \<parallel>\<^sub>B Const 4 (*landing, uint32(4), r=1/10s*))
      = FBlock (\<lambda>x n. True) (1) (2) 
        (\<lambda>x n. (((f_UnitDelay 0 \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
               ((f_Const 4 \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n))"
      using SimBlock_UnitDelay SimBlock_Const apply (simp add: FBlock_parallel_comp f_sim_blocks)
      by (simp add: numeral_2_eq_2)
    have f1_0: "... = FBlock (\<lambda>x n. True) (1) (2) 
        (\<lambda>x n. ([if n = 0 then 0 else hd(x (n-1)), 4]))"
      using f_UnitDelay_def f_Const_def apply (auto)
      proof -
        { fix nn :: nat and rrs :: "nat \<Rightarrow> real list"
          have "\<forall>rs n. hd (take n rs) = (hd rs::real) \<or> take n rs = []"
            by (metis append_take_drop_id hd_append2)
          then have "FBlock (\<lambda>f n. True) (Suc 0) 2 (\<lambda>f n. [if n = 0 then 0 else hd (take (Suc 0) (f (n - 1))), 4]) 
              = FBlock (\<lambda>f n. True) (Suc 0) 2 (\<lambda>f n. [if n = 0 then 0 else hd (f (n - 1)), 4]) \<or> 
                [if nn = 0 then 0 else hd (take (Suc 0) (rrs (nn - 1))), 4] = [if nn = 0 then 0 else hd (rrs (nn - 1)), 4]"
            by force }
        then show "FBlock (\<lambda>f n. True) (Suc 0) 2 (\<lambda>f n. [if n = 0 then 0 else hd (take (Suc 0) (f (n - 1))), 4]) 
              = FBlock (\<lambda>f n. True) (Suc 0) 2 (\<lambda>f n. [if n = 0 then 0 else hd (f (n - 1)), 4])"
          by presburger
      qed
    have simblock_f1: "SimBlock 1 2 (FBlock (\<lambda>x n. True) (1) (2) 
        (\<lambda>x n. ([if n = 0 then 0 else hd(x (n-1)), 4])))"
      using SimBlock_UnitDelay SimBlock_Const f1 f1_0 apply (simp add: SimBlock_FBlock_parallel_comp f_sim_blocks)
      by (smt One_nat_def SimBlock_FBlock_parallel_comp Suc_1 Suc_eq_plus1 add.right_neutral)
    (* ((UnitDelay 0 (*IC = 0, r=1/10s*) \<parallel>\<^sub>B Const 4 (*landing, uint32(4), r=1/10s*)) ;; RopEQ) *)
    have f2: "((UnitDelay 0 (*IC = 0, r=1/10s*) \<parallel>\<^sub>B Const 4 (*landing, uint32(4), r=1/10s*)) ;; RopEQ) = 
      (FBlock (\<lambda>x n. True) (1) (2) (\<lambda>x n. ([if n = 0 then 0 else hd(x (n-1)), 4]))) ;; RopEQ"
      using f1 f1_0 by simp
    then have f2_0: "... = 
      (FBlock (\<lambda>x n. True) (1) (1) (f_RopEQ o (\<lambda>x n. ([if n = 0 then 0 else hd(x (n-1)), 4]))))"
      using simblock_f1 SimBlock_RopEQ FBlock_seq_comp by (simp add: RopEQ_def)
    then have f2_1: "... = (FBlock (\<lambda>x n. True) (1) (1) 
      (\<lambda>x n. ([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0])))"
      proof -
        have "\<forall>x n. (f_RopEQ o (\<lambda>x n. ([if n = 0 then 0 else hd(x (n-1)), 4]))) x n
          = (\<lambda>x n. ([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0])) x n"
          using f_RopEQ_def by auto
        then show ?thesis
          by presburger
      qed
    have simblock_f2: "SimBlock 1 1 (FBlock (\<lambda>x n. True) (1) (1) 
      (\<lambda>x n. ([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0])))"
      using f2 f2_0 f2_1 by (smt RopEQ_def SimBlock_FBlock_seq_comp SimBlock_RopEQ simblock_f1)
    (* (Id \<parallel>\<^sub>B Const 8 (*ground, uint32(8), r=1/10s*)) *)
    have f3: "(Id \<parallel>\<^sub>B Const 8 (*ground, uint32(8), r=1/10s*)) 
      = FBlock (\<lambda>x n. True) (1) (2) 
        (\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
               ((f_Const 8 \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n))"
      using SimBlock_Id SimBlock_Const apply (simp add: FBlock_parallel_comp f_sim_blocks)
      by (simp add: numeral_2_eq_2)
    then have f3_0: "... = FBlock (\<lambda>x n. True) (1) (2) (\<lambda>x n. ([hd(x n), 8]))"
      proof -
        have "\<forall>x n. ((\<lambda>x n. (((f_Id \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
               ((f_Const 8 \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)) x n
          = (\<lambda>x n. ([hd(x n), 8])) x n)"
          using f_Id_def f_Const_def
          proof -
          { fix rrs :: "nat \<Rightarrow> real list" and nn :: nat
            have "\<forall>rs. hd (take 1 rs) = (hd rs::real) \<or> rs = []"
                by (metis Suc_eq_plus1 add.left_neutral list.sel(1) take_Suc)
              then have "(f_Id \<circ> (\<lambda>f n. take 1 (f n))) rrs nn @ (f_Const 8 \<circ> (\<lambda>f n. drop 1 (f n))) rrs nn = [hd (rrs nn), 8]"
                using f_Const_def f_Id_def by auto }
            then show ?thesis
              by fastforce
          qed
        then show ?thesis
          by simp
      qed
    have simblock_f3: "SimBlock 1 2 (FBlock (\<lambda>x n. True) (1) (2) (\<lambda>x n. ([hd(x n), 8])))"
      by (metis (no_types, lifting) One_nat_def SimBlock_Const SimBlock_Id SimBlock_FBlock_parallel_comp 
          Suc_1 Suc_eq_plus1 add.commute f3 f3_0 simu_contract_real.Const_def simu_contract_real.Id_def)
    (* ((Id \<parallel>\<^sub>B Const 8 (*ground, uint32(8), r=1/10s*)) ;; RopEQ) *)
    have f4: "((Id \<parallel>\<^sub>B Const 8 (*ground, uint32(8), r=1/10s*)) ;; RopEQ)
      = FBlock (\<lambda>x n. True) (1) (2) (\<lambda>x n. ([hd(x n), 8])) ;; RopEQ"
      using f3 f3_0 by simp
    then have f4_0: "... = FBlock (\<lambda>x n. True) (1) (1) (f_RopEQ o (\<lambda>x n. ([hd(x n), 8])))"
      using simblock_f3 SimBlock_RopEQ FBlock_seq_comp by (simp add: RopEQ_def)
    then have f4_1: "... = FBlock (\<lambda>x n. True) (1) (1) (\<lambda>x n. ([if hd(x n) = 8 then 1 else 0]))"
      using f_RopEQ_def by (metis (mono_tags, lifting) comp_apply list.sel(1) list.sel(3))
    have simblock_f4: "SimBlock 1 1 
        (FBlock (\<lambda>x n. True) (1) (1) (\<lambda>x n. ([if hd(x n) = 8 then 1 else 0])))"
      using simblock_f3 SimBlock_RopEQ by (metis RopEQ_def SimBlock_FBlock_seq_comp f4_0 f4_1)
    (* (
      ((UnitDelay 0 (*IC = 0, r=1/10s*) \<parallel>\<^sub>B Const 4 (*landing, uint32(4), r=1/10s*)) ;; RopEQ)
      \<parallel>\<^sub>B
      ((Id \<parallel>\<^sub>B Const 8 (*ground, uint32(8), r=1/10s*)) ;; RopEQ)
      ) *)
    have f5: "(
      ((UnitDelay 0 (*IC = 0, r=1/10s*) \<parallel>\<^sub>B Const 4 (*landing, uint32(4), r=1/10s*)) ;; RopEQ)
      \<parallel>\<^sub>B
      ((Id \<parallel>\<^sub>B Const 8 (*ground, uint32(8), r=1/10s*)) ;; RopEQ))
      = (FBlock (\<lambda>x n. True) (1) (1) (\<lambda>x n. ([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0])))
        \<parallel>\<^sub>B 
        (FBlock (\<lambda>x n. True) (1) (1) (\<lambda>x n. ([if hd(x n) = 8 then 1 else 0])))"
      using f2 f2_1 f4 f4_1 f2_0 f4_0 by auto
    then have f5_0: "... = FBlock (\<lambda>x n. True) (2) (2) 
        (\<lambda>x n. ((((\<lambda>x n. ([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0])) 
                    \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
               (( (\<lambda>x n. ([if hd(x n) = 8 then 1 else 0])) 
                    \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n))"
      using simblock_f2 simblock_f4 apply (simp add: FBlock_parallel_comp f_sim_blocks)
      by (simp add: numeral_2_eq_2)
    then have f5_1: "... = FBlock (\<lambda>x n. True) (2) (2) 
        (\<lambda>x n. (([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0, if (x n)!1 = 8 then 1 else 0])))"
      proof -
        show ?thesis
          apply (simp add: FBlock_def)
          apply (rel_simp)
          apply (rule conjI)
          apply (clarify)
          apply (rule conjI)
          apply (clarify)
          apply (rule iffI)
          apply (clarify)
          apply (subgoal_tac "\<forall>x. length(inouts\<^sub>v x) = 2")
          apply (rule conjI)
          apply (clarify)
          using hd_drop_m hd_take_m apply (metis Suc_1 Suc_eq_plus1 add.left_neutral lessI)
          using hd_drop_m hd_take_m apply simp
          using neq0_conv apply blast
          apply (clarify)
          apply (subgoal_tac "\<forall>x. length(inouts\<^sub>v x) = 2")
          apply (rule conjI)
          apply (clarify)
          using hd_drop_m hd_take_m apply (metis Suc_1 Suc_eq_plus1 add.left_neutral lessI)
          using hd_drop_m hd_take_m apply simp
          using neq0_conv apply blast
          apply (clarify)
          apply (rule iffI)
          apply (clarify)
          apply (subgoal_tac "\<forall>x. length(inouts\<^sub>v x) = 2")
          apply (rule conjI)
          apply (clarify)
          using hd_drop_m hd_take_m apply (metis Suc_1 Suc_eq_plus1 add.left_neutral lessI)
          using hd_drop_m hd_take_m apply simp
          using neq0_conv apply blast
          apply (clarify)
          apply (subgoal_tac "\<forall>x. length(inouts\<^sub>v x) = 2")
          apply (rule conjI)
          apply (clarify)
          using hd_drop_m hd_take_m apply (metis Suc_1 Suc_eq_plus1 add.left_neutral lessI)
          using hd_drop_m hd_take_m apply simp
          using neq0_conv apply blast
          apply (clarify)
          apply (rule conjI)
          apply (clarify)
          apply (rule iffI)
          apply (clarify)
          apply (subgoal_tac "\<forall>x. length(inouts\<^sub>v x) = 2")
          apply (rule conjI)
          apply (clarify)
          using hd_drop_m hd_take_m apply (metis Suc_1 Suc_eq_plus1 add.left_neutral lessI)
          using hd_drop_m hd_take_m apply simp
          using neq0_conv apply blast
          apply (clarify)
          apply (subgoal_tac "\<forall>x. length(inouts\<^sub>v x) = 2")
          apply (rule conjI)
          apply (clarify)
          using hd_drop_m hd_take_m apply (metis Suc_1 Suc_eq_plus1 add.left_neutral lessI)
          using hd_drop_m hd_take_m apply simp
          using neq0_conv apply blast
          apply (clarify)
          apply (rule iffI)
          apply (clarify)
          apply (subgoal_tac "\<forall>x. length(inouts\<^sub>v x) = 2")
          apply (rule conjI)
          apply (clarify)
          using hd_drop_m hd_take_m apply (metis Suc_1 Suc_eq_plus1 add.left_neutral lessI)
          using hd_drop_m hd_take_m apply simp
          apply metis
          using neq0_conv apply blast
          apply (clarify)
          apply (subgoal_tac "\<forall>x. length(inouts\<^sub>v x) = 2")
          apply (rule conjI)
          apply (clarify)
          using hd_drop_m hd_take_m apply (metis Suc_1 Suc_eq_plus1 add.left_neutral lessI)
          using hd_drop_m hd_take_m apply simp
          apply metis
          using neq0_conv by blast
      qed
    have simblock_f5: "SimBlock 2 2 (FBlock (\<lambda>x n. True) (2) (2) 
        (\<lambda>x n. (([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0, if (x n)!1 = 8 then 1 else 0]))))"
      using simblock_f2 simblock_f4 SimBlock_FBlock_parallel_comp f5 f5_0 f5_1
      by (metis (no_types, lifting) one_add_one)
  
    have f6: "post_mode = Split2 ;; (FBlock (\<lambda>x n. True) (2) (2) 
        (\<lambda>x n. (([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0, if (x n)!1 = 8 then 1 else 0]))))"
      using f5 f5_0 f5_1 post_mode_def by auto
    then have f6_0: "... = (FBlock (\<lambda>x n. True) (1) (2) (
      (\<lambda>x n. (([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0, if (x n)!1 = 8 then 1 else 0]))) o f_Split2))"
      using SimBlock_Split2 simblock_f5 by (simp add: FBlock_seq_comp f_sim_blocks)
    then have f6_1: "... = (FBlock (\<lambda>x n. True) (1) (2)
      (\<lambda>x n. (([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0, if hd(x n) = 8 then 1 else 0]))))"
      proof -
        have "\<forall>x n. ((\<lambda>x n. (([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0, 
                        if (x n)!1 = 8 then 1 else 0]))) o f_Split2) x n
          = (\<lambda>x n. (([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0, 
                        if hd(x n) = 8 then 1 else 0]))) x n"
          using f_Split2_def by simp
        then show ?thesis
          by metis
      qed
    then show ?thesis
      using f6 f6_0 by auto
  qed

text {* Finally, @{text "post_landing_finalize"} is the composition of subsystems defined previously 
 and other blocks. It is shown in @{text "post_landing_finalize_1"}. *}
abbreviation "post_landing_finalize_part1 \<equiv> (
    (
      (
        (
          Split2 (* door_closed (boolean, 1/10s) is split into two *) 
          \<parallel>\<^sub>B
          Id (* door_open_time: double *)
        ) ;; Router 3 [0,2,1]
      )
      \<parallel>\<^sub>B 
      post_mode
    )
    \<parallel>\<^sub>B
    (
       (UnitDelay 1.0 ;; LopNOT) (* ac_on_ground *)
       \<parallel>\<^sub>B
       (UnitDelay 0) (* Delay2 *)
    )
  )"

abbreviation "post_landing_finalize_part2 \<equiv> ( 
      (
         (LopNOT)
         \<parallel>\<^sub>B
         (Id) (* door_open_time: double *)
      ) ;; variableTimer
    )"

abbreviation "post_landing_finalize_part3 \<equiv> (
      (
         (LopAND 3)
         \<parallel>\<^sub>B
         (LopOR 2)
      ) ;; latch
    )"


definition "post_landing_finalize_1 \<equiv> 
(
  post_landing_finalize_part1 ;;
  (
    post_landing_finalize_part2
    \<parallel>\<^sub>B
    post_landing_finalize_part3
  ) ;; LopAND 2;; rise1Shot ;; Split2
) f\<^sub>D (4, 1)
"

text {* Simplified design corresponding to a part of the diagram from inputs to @{text "variableTimer"}. *}
abbreviation "plf_vt_simp \<equiv> \<lambda>x na. if (if hd(x na) = 0
                   then (if na = 0 then 0
                         else min (vT_fd_sol_1
                                 (\<lambda>n1. (\<lambda>na. real_of_int
                                        (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) n1)
                                 (\<lambda>n1. (if hd(x n1) = 0 then 1::real else 0)) (na - 1))
                            ((\<lambda>na. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>))))
                                  (na - 1))) + 1::real
                    else 0) > (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) 
          then 1::real else 0"

text {* Simplified design corresponding to a part of the diagram from inputs to @{text "latch"}. *}
abbreviation "plf_latch_simp \<equiv> \<lambda>x na. (latch_rec_calc_output 
                      (\<lambda>n1. (if hd(x n1) = 0 \<or> n1 = 0 \<or> (x (n1-1))!2 \<noteq> 4 \<or> (x n1)!2 \<noteq> 8
                          then 0 else 1::real)) 
                      (\<lambda>n1. (if ((n1 = 0) \<or> ((x (n1 - 1))!3 \<noteq> 0 \<and> (x (n1 - 1))!4 = 0))
                          then 0 else 1::real))
                      (na))"

text {* A function for the simplified design corresponding to a part of the diagram from inputs to 
outputs but without the feedback from one of outputs. *}
abbreviation "plf_rise1shot_simp_f \<equiv> (\<lambda>x n. [if (((plf_vt_simp x n) \<noteq> 0 \<and> (plf_latch_simp x n) \<noteq> 0) \<and> 
                    (n > 0 \<and> ((plf_vt_simp x (n-1)) = 0 \<or> (plf_latch_simp x (n-1)) = 0))) then 1 else 0,
                          if (((plf_vt_simp x n) \<noteq> 0 \<and> (plf_latch_simp x n) \<noteq> 0) \<and> 
                    (n > 0 \<and> ((plf_vt_simp x (n-1)) = 0 \<or> (plf_latch_simp x (n-1)) = 0))) then 1 else 0])"

text {* Simplified design corresponding to a part of the diagram from inputs to outputs but without 
the feedback from one of outputs. *}
definition "plf_rise1shot_simp \<equiv> FBlock (\<lambda>x n. True) 5 2 plf_rise1shot_simp_f"

(*
abbreviation "f12_f_1' \<equiv> \<lambda> door_closed door_open_time na. 
              if (if door_closed na = 0
                   then (if na = 0 then 0
                         else min (vT_fd_sol_1
                                 (\<lambda>n1. (\<lambda>na. real_of_int
                                        (int32 (RoundZero (real_of_int \<lceil>Rate * max (door_open_time na) 0\<rceil>)))) n1)
                                 (\<lambda>n1. (if door_closed n1 = 0 then 1::real else 0)) (na - 1))
                            ((\<lambda>na. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (door_open_time na) 0\<rceil>))))
                                  (na - 1))) + 1::real
                    else 0) > (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (door_open_time na) 0\<rceil>)))) 
          then 1::real else 0"
(*
abbreviation "f12_f_2' \<equiv> \<lambda> door_closed mode ac_on_ground xx na. (latch_rec_calc_output 
                      (\<lambda>n1. (if door_closed n1 = 0 \<or> n1 = 0 \<or> mode (n1-1) \<noteq> 4 \<or> mode n1 \<noteq> 8
                          then 0 else 1::real)) 
                      (\<lambda>n1. (if ((n1 = 0) \<or> (ac_on_ground (n1 - 1) \<noteq> 0 \<and> xx (n1 - 1) = 0))
                          then 0 else 1::real))
                      (na))"
*)

fun latch_rec_calc_output':: "(nat \<Rightarrow> real) \<Rightarrow> 
  (nat \<Rightarrow> real) \<Rightarrow> 
  (nat \<Rightarrow> real) \<Rightarrow>
  (nat \<Rightarrow> real) \<Rightarrow>
  nat \<Rightarrow> real" where
"latch_rec_calc_output' door_closed mode ac_on_ground xx 0 = 0" |
    (*(if R 0 = 0 then (if S 0 = 0 then 0 else 1.0) else 0 )
      R 0 and S 0 are always 0 *) 
"latch_rec_calc_output' door_closed mode ac_on_ground xx (Suc n) = 
(* (if R (Suc n) = 0 then (if S (Suc n) = 0 then (latch_rec_calc_output S R (n)) else 1.0) else 0) *)
    (if (ac_on_ground n \<noteq> 0 \<and> xx n = 0)
     then 
      (if (door_closed (Suc n) = 0 \<or> mode n \<noteq> 4 \<or> mode (Suc n) \<noteq> 8)
       then
        (latch_rec_calc_output' door_closed mode ac_on_ground xx (n))
       else 1.0)
     else 0
    )"

text {* Congruence Rules *}
lemma latch_rec_calc_output'_cong:
  assumes "x = x'" "y = y'" "z = z'" "u = u'" "v = v'"
  shows "latch_rec_calc_output' x y z u v = latch_rec_calc_output' x' y' z' u' v'"
  by (simp add: assms)  

(* ?f15 f\<^sub>D (4, 1) *)
(* (SOME (xx::nat \<Rightarrow> real). (xx n = (if (((f12_f_1 x n) \<noteq> 0 \<and> (f12_f_2' xx x n) \<noteq> 0) \<and> 
                    (n > 0 \<and> ((f12_f_1 x (n-1)) = 0 \<or> (f12_f_2' xx x (n-1)) = 0))) then 1 else 0))) *)
(* calculate current output according to previous inputs *)
(* It is not possible to define the solution using fun since it cannot find the terminatin order
because (post_fd_sol_1 door_closed door_open_time mode ac_on_ground) appearing in latch_rec_calc_output'
isn't decreased (we need a function (nat \<Rightarrow> real) as xx for latch_rec_calc_output')
*)
(*
fun post_fd_sol_1:: "(nat \<Rightarrow> real) (* input 0: door_closed *)
  \<Rightarrow> (nat \<Rightarrow> real) (* input 1: door_open_time *)
  \<Rightarrow> (nat \<Rightarrow> real) (* input 2: mode *)
  \<Rightarrow> (nat \<Rightarrow> real) (* input 3: ac_on_ground *)
  \<Rightarrow> nat 
  \<Rightarrow> real" where
"post_fd_sol_1 door_closed door_open_time mode ac_on_ground 0 = 
    (0)" |
"post_fd_sol_1 door_closed door_open_time mode ac_on_ground (Suc n) = 
    (if (((f12_f_1' door_closed door_open_time (Suc n)) \<noteq> 0 \<and> 
          (latch_rec_calc_output' door_closed mode ac_on_ground 
            (post_fd_sol_1 door_closed door_open_time mode ac_on_ground) (Suc n)) \<noteq> 0) \<and> 
       ((f12_f_1' door_closed door_open_time n = 0) \<or> 
        (latch_rec_calc_output' door_closed mode ac_on_ground 
            (post_fd_sol_1 door_closed door_open_time mode ac_on_ground) n) = 0))
    then 1 else 0)"
*)

text {* The solution for the last feedback. *}
(* Use function, we need to prove its termination over high order recursion and it is complicated.
  Maybe the better way is to apply compositional reason.
*)
function post_fd_sol_1 :: "(nat \<Rightarrow> real) (* input 0: door_closed *)
  \<Rightarrow> (nat \<Rightarrow> real) (* input 1: door_open_time *)
  \<Rightarrow> (nat \<Rightarrow> real) (* input 2: mode *)
  \<Rightarrow> (nat \<Rightarrow> real) (* input 3: ac_on_ground *)
  \<Rightarrow> nat 
  \<Rightarrow> real" where
"post_fd_sol_1 door_closed door_open_time mode ac_on_ground n =
  (if (n = 0) then 0
  else 
    (if (((f12_f_1' door_closed door_open_time (n)) \<noteq> 0 \<and> 
          (latch_rec_calc_output' door_closed mode ac_on_ground 
            (post_fd_sol_1 door_closed door_open_time mode ac_on_ground) (n)) \<noteq> 0) \<and> 
       ((f12_f_1' door_closed door_open_time (n-1) = 0) \<or> 
        (latch_rec_calc_output' door_closed mode ac_on_ground 
            (post_fd_sol_1 door_closed door_open_time mode ac_on_ground) (n-1)) = 0))
    then 1.0 else 0))"
  using prod_cases5 apply blast
  by blast
(*termination 
  apply (relation "measure (\<lambda> (door_closed, door_open_time, mode, ac_on_ground, n). n)")
  apply simp
  sorry
*)

subsubsection {* @{text "post_landing_finalize_part1"} *}
text {* Simplified @{text "post_landing_finalize_part1"} *}
abbreviation "plf1_1_f \<equiv> (\<lambda>x n. [hd(x n), hd(tl(x n)), hd(x n), 
            if (n > 0 \<and> (x (n-1))!2 = 4) then 1::real else 0,
            if (x n)!2 = 8 then 1 else 0,
            (if n = 0 then 0 else (if (x (n - 1))!3 = 0 then 1 else 0)), 
            if n = 0 then 0 else (x (n - 1))!4])"
abbreviation "plf1_1 \<equiv> FBlock (\<lambda>x n. True) 5 7 plf1_1_f"

lemma post_landing_finalize_part1_simp_and_simblock:
  "post_landing_finalize_part1 = plf1_1 \<and> SimBlock 5 7 plf1_1"
  proof -
    (*
      (
        Split2 (* door_closed (boolean, 1/10s) is split into two *) 
        \<parallel>\<^sub>B
        Id (* door_open_time: double *)
      ) ;; Router 3 [0,2,1]
    *)
    let ?f1_f = "(\<lambda>x n. [hd(x n), hd(x n), hd(tl(x n))])"
    let ?f1 = "FBlock (\<lambda>x n. True) 2 3 ?f1_f"
    have f1: "Split2 (* door_closed (boolean, 1/10s) is split into two *) 
        \<parallel>\<^sub>B Id (* door_open_time: double *) 
      = FBlock (\<lambda>x n. True) (1+1) (2+1) 
        (\<lambda>x n. (((f_Split2 \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                ((f_Id \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)) "
      using SimBlock_Id SimBlock_Split2 FBlock_parallel_comp 
      by (simp add: Split2_def simu_contract_real.Id_def)
    then have f1_0: "... = ?f1"
      proof -
        have "\<forall>x n. ((\<lambda>x n. (((f_Split2 \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                ((f_Id \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)) x n)
          = (?f1_f x n)"
          using f_Id_def f_Split2_def by (simp add: drop_Suc hd_take_m)
        then show ?thesis
          apply (simp)
          by (simp add: numeral_2_eq_2)
      qed
    have simblock_f1: "SimBlock 2 3 (?f1)"
      using SimBlock_Id SimBlock_Split2 SimBlock_FBlock_parallel_comp 
      by (metis (no_types, lifting) One_nat_def Split2_def Suc_1 Suc_eq_plus1 f1 f1_0 
          numeral_3_eq_3 simu_contract_real.Id_def)
    (* (
        Split2 (* door_closed (boolean, 1/10s) is split into two *) 
        \<parallel>\<^sub>B
        Id (* door_open_time: double *)
      ) ;; Router 3 [0,2,1] 
    *)
    let ?f2_f = "(\<lambda>x n. [hd(x n), hd(tl(x n)), hd(x n)])"
    let ?f2 = "FBlock (\<lambda>x n. True) (2) (3) ?f2_f"
    have f2: "(Split2 \<parallel>\<^sub>B Id) ;; Router 3 [0,2,1] = ?f1 ;; Router 3 [0,2,1]"
      using f1 f1_0 by auto
    then have f2_0: "... = FBlock (\<lambda>x n. True) (2) (3) (f_Router [0,2,1] o ?f1_f)"
      using simblock_f1 Router_def SimBlock_Router FBlock_seq_comp by simp
    then have f2_1: "... = ?f2"
      proof -
        have "\<forall>x n. (f_Router [0,2,1] o ?f1_f) x n = ?f2_f x n"
          using f_Router_def by (simp)
        then show ?thesis
          by presburger
      qed
    have simblock_f2: "SimBlock 2 3 ?f2"
      using simblock_f1 SimBlock_Router SimBlock_FBlock_seq_comp
      by (metis (no_types, lifting) Router_def f2_0 f2_1 length_Cons list.size(3) numeral_3_eq_3)
    (* (
      (
        (
          Split2 (* door_closed (boolean, 1/10s) is split into two *) 
          \<parallel>\<^sub>B
          Id (* door_open_time: double *)
        ) ;; Router 3 [0,2,1]
      )
      \<parallel>\<^sub>B 
      post_mode
    ) *)
    let ?post_mode_f = 
      "(\<lambda>x n. (([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0, if hd(x n) = 8 then 1 else 0])))"
    let ?post_mode = "(FBlock (\<lambda>x n. True) (1) (2) ?post_mode_f)"
    have simblock_post_mode: "SimBlock 1 2 (?post_mode)"
      apply (rule SimBlock_FBlock)
      apply (rule_tac x = "\<lambda>na. [4]" in exI)
      apply (rule_tac x = "\<lambda>na. [if na > 0 then 1 else 0, 0]" in exI)
      apply (simp add: f_blocks)
      by (simp add: f_blocks)
    let ?f3_f = "(\<lambda>x n. [hd(x n), hd(tl(x n)), hd(x n), 
            if (n > 0 \<and> (x (n-1))!2 = 4) then 1::real else 0,
            if (x n)!2 = 8 then 1 else 0])"
    let ?f3 = "FBlock (\<lambda>x n. True) 3 5 ?f3_f"
    have f3: "((( Split2 (* door_closed (boolean, 1/10s) is split into two *) 
                \<parallel>\<^sub>B
                Id (* door_open_time: double *)
              ) ;; Router 3 [0,2,1])
              \<parallel>\<^sub>B post_mode) = ?f2 \<parallel>\<^sub>B ?post_mode"
      using f2 f2_0 f2_1 post_mode_simp by auto
    then have f3_0: "... = FBlock (\<lambda>x n. True) (2+1) (3+2) 
        (\<lambda>x n. (((?f2_f \<circ> (\<lambda>xx nn. take 2 (xx nn))) x n) @ 
                ((?post_mode_f \<circ> (\<lambda>xx nn. drop 2 (xx nn)))) x n))"
      using simblock_post_mode simblock_f1 FBlock_parallel_comp simblock_f2 by blast
    then have f3_1: "... = FBlock (\<lambda>x n. True) (2+1) (3+2) ?f3_f"
      proof -
        show ?thesis
          apply (simp add: FBlock_def)
          apply (rel_simp)
          apply (rule conjI, clarify)
          apply (rule conjI, clarify)
          apply (rule iffI, clarify)
          defer
          apply (clarify)
          defer 
          apply (clarify, rule iffI, clarify)
          apply (metis hd_drop_conv_nth lessI numeral_2_eq_2 numeral_3_eq_3)
          apply (clarify)
          apply (simp add: hd_drop_conv_nth)
          apply (clarify, rule conjI, clarify)
          apply (rule iffI, clarify)
          apply (metis hd_drop_conv_nth lessI numeral_2_eq_2 numeral_3_eq_3)
          apply (clarify)
          apply (simp add: hd_drop_conv_nth)
          apply (clarify, rule iffI, clarify)
          defer
          apply (clarify)
          defer
          proof -
            fix ok\<^sub>v ok\<^sub>v'::bool and inouts\<^sub>v  inouts\<^sub>v'::"nat \<Rightarrow> real list" and x
            assume a1: "\<forall>x. (hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 1] =
               inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 1] =
               inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 1] =
               inouts\<^sub>v' x)) \<and>
             (\<not> hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 0] =
               inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 1] =
               inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 0] =
               inouts\<^sub>v' x))"
            from a1 have len_3: "\<forall>x. length(inouts\<^sub>v x) = 3"
              by (metis neq0_conv)
            have drop_2: "\<forall>x. (hd (drop 2 (inouts\<^sub>v' x)) = (inouts\<^sub>v' x)!2)"
              using len_3 hd_drop_m
              by (metis Suc_eq_plus1 Suc_le_eq a1 add_Suc_right add_diff_cancel_right' diff_le_self 
                  hd_drop_conv_nth neq0_conv one_plus_numeral one_plus_numeral_commute semiring_norm(2) 
                  semiring_norm(3) semiring_norm(4))
            have take_2: "\<forall>x. hd (take 2 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_3 hd_take_m by simp
            have take_tl_2: "\<forall>x. hd (tl (take 2 (inouts\<^sub>v x))) = hd(tl(inouts\<^sub>v x))"
              using len_3 hd_tl_take_m by simp
            show "(inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 1] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 1] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0] = inouts\<^sub>v' x))"
            using drop_2 take_2 take_tl_2
            by (metis One_nat_def Suc_1 a1 hd_drop_conv_nth len_3 lessI numeral_3_eq_3)
          next
            fix ok\<^sub>v ok\<^sub>v'::bool and inouts\<^sub>v  inouts\<^sub>v'::"nat \<Rightarrow> real list" and x
            assume a1: "\<forall>x. (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 1] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 1] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0] = inouts\<^sub>v' x))"
            from a1 have len_3: "\<forall>x. length(inouts\<^sub>v x) = 3"
              by (metis neq0_conv)
            have drop_2: "\<forall>x. (hd (drop 2 (inouts\<^sub>v' x)) = (inouts\<^sub>v' x)!2)"
              using len_3 hd_drop_m
              by (metis Suc_eq_plus1 Suc_le_eq a1 add_Suc_right add_diff_cancel_right' diff_le_self 
                  hd_drop_conv_nth neq0_conv one_plus_numeral one_plus_numeral_commute semiring_norm(2) 
                  semiring_norm(3) semiring_norm(4))
            have take_2: "\<forall>x. hd (take 2 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_3 hd_take_m by simp
            have take_tl_2: "\<forall>x. hd (tl (take 2 (inouts\<^sub>v x))) = hd(tl(inouts\<^sub>v x))"
              using len_3 hd_tl_take_m by simp
            show "(hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 1] =
               inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 1] =
               inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 1] =
               inouts\<^sub>v' x)) \<and>
             (\<not> hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 0] =
               inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 1] =
               inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 0] =
               inouts\<^sub>v' x))"
            using drop_2 take_2 take_tl_2
            by (metis One_nat_def Suc_1 a1 hd_drop_conv_nth len_3 lessI numeral_3_eq_3)
          next
            fix ok\<^sub>v ok\<^sub>v'::bool and inouts\<^sub>v  inouts\<^sub>v'::"nat \<Rightarrow> real list" and x::nat
            assume a1: "\<forall>x. (hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 1] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 0] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 0] = inouts\<^sub>v' x))"
            assume a2: "\<not> hd (drop 2 (inouts\<^sub>v 0)) = 8"
            assume a3: "\<not> inouts\<^sub>v 0!(2) = 8"
            from a1 have len_3: "\<forall>x. length(inouts\<^sub>v x) = 3"
              by (metis neq0_conv)
            have drop_2: "\<forall>x. (hd (drop 2 (inouts\<^sub>v' x)) = (inouts\<^sub>v' x)!2)"
              using len_3 hd_drop_m
              by (metis Suc_eq_plus1 Suc_le_eq a1 add_Suc_right add_diff_cancel_right' diff_le_self 
                  hd_drop_conv_nth neq0_conv one_plus_numeral one_plus_numeral_commute semiring_norm(2) 
                  semiring_norm(3) semiring_norm(4))
            have take_2: "\<forall>x. hd (take 2 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_3 hd_take_m by simp
            have take_tl_2: "\<forall>x. hd (tl (take 2 (inouts\<^sub>v x))) = hd(tl(inouts\<^sub>v x))"
              using len_3 hd_tl_take_m by simp
            show "(inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0] = inouts\<^sub>v' x))"
            using drop_2 take_2 take_tl_2
            by (metis One_nat_def Suc_1 a1 hd_drop_conv_nth len_3 lessI numeral_3_eq_3)
          next
            fix ok\<^sub>v ok\<^sub>v'::bool and inouts\<^sub>v  inouts\<^sub>v'::"nat \<Rightarrow> real list" and x
            assume a1: "\<forall>x. (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and> length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and> length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0] = inouts\<^sub>v' x))"
            from a1 have len_3: "\<forall>x. length(inouts\<^sub>v x) = 3"
              by (metis neq0_conv)
            have drop_2: "\<forall>x. (hd (drop 2 (inouts\<^sub>v' x)) = (inouts\<^sub>v' x)!2)"
              using len_3 hd_drop_m
              by (metis Suc_eq_plus1 Suc_le_eq a1 add_Suc_right add_diff_cancel_right' diff_le_self 
                  hd_drop_conv_nth neq0_conv one_plus_numeral one_plus_numeral_commute semiring_norm(2) 
                  semiring_norm(3) semiring_norm(4))
            have take_2: "\<forall>x. hd (take 2 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_3 hd_take_m by simp
            have take_tl_2: "\<forall>x. hd (tl (take 2 (inouts\<^sub>v x))) = hd(tl(inouts\<^sub>v x))"
              using len_3 hd_tl_take_m by simp
            show "(hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 1] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 0] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 0] = inouts\<^sub>v' x))"
            using drop_2 take_2 take_tl_2
            by (metis One_nat_def Suc_1 a1 hd_drop_conv_nth len_3 lessI numeral_3_eq_3)
          qed
      qed
    have simblock_f3: "SimBlock 3 5 (?f3)"
      using simblock_f2 simblock_post_mode SimBlock_FBlock_parallel_comp
      by (smt Suc_eq_plus1 add_Suc f3_0 f3_1 numeral_2_eq_2 numeral_3_eq_3 numeral_code(3))
    (* 
       (UnitDelay 1.0 ;; LopNOT)
    *)
    let ?f4_f = "(\<lambda>x n. [(if n = 0 then 0 else (if hd(x (n-1)) = 0 then 1 else 0))])"
    let ?f4 = "FBlock (\<lambda>x n. True) 1 1 ?f4_f"
    have f4: "(UnitDelay 1.0 ;; LopNOT) = FBlock (\<lambda>x n. True) 1 1 (f_LopNOT o f_UnitDelay 1.0)"
      using SimBlock_UnitDelay SimBlock_LopNOT FBlock_seq_comp by (simp add: LopNOT_def UnitDelay_def)
    then have f4_0: "... = FBlock (\<lambda>x n. True) 1 1 ?f4_f"
      proof -
        have "\<forall>x n. (f_LopNOT o f_UnitDelay 1.0) x n = ?f4_f x n"
          using f_LopNOT_def f_UnitDelay_def by simp
        then show ?thesis
          by presburger
      qed
    have simblock_f4: "SimBlock 1 1 ?f4"
      using SimBlock_UnitDelay SimBlock_LopNOT SimBlock_FBlock_seq_comp
      by (metis (no_types, lifting) LopNOT_def UnitDelay_def f4 f4_0)
    (* (UnitDelay 1.0 ;; LopNOT)
       \<parallel>\<^sub>B
       (UnitDelay 0) (* Delay2 *) *)
    let ?f5_f = "(\<lambda>x n. [(if n = 0 then 0 else (if hd(x (n-1)) = 0 then 1 else 0)), 
      if n = 0 then 0 else hd(tl(x (n - 1)))])"
    let ?f5 = "FBlock (\<lambda>x n. True) 2 2 ?f5_f"
    have f5: "((UnitDelay 1.0 ;; LopNOT)
             \<parallel>\<^sub>B
             (UnitDelay 0) (* Delay2 *))
      = ?f4 \<parallel>\<^sub>B (UnitDelay 0)"
      using f4 f4_0 by auto
    then have f5_0: "... = FBlock (\<lambda>x n. True) 2 2 
        (\<lambda>x n. (((?f4_f \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                ((f_UnitDelay 0 \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n))"
      using simblock_f4 SimBlock_UnitDelay FBlock_parallel_comp apply (simp add: UnitDelay_def)
      by (simp add: numeral_2_eq_2)
    then have f5_1: "... = ?f5"
      proof -
        have "\<forall>x n. (\<lambda>x n. (((?f4_f \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                ((f_UnitDelay 0 \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n))  x n
          = ?f5_f x n"
          using f_UnitDelay_def apply (simp)
          apply (rule allI)+
          apply (rule conjI, clarify)
          apply (simp add: drop_Suc hd_take_m)
          by (simp add: drop_Suc hd_take_m)
        then show ?thesis
          by presburger
      qed
    have simblock_f5: "SimBlock 2 2 ?f5"
      using simblock_f4 SimBlock_UnitDelay SimBlock_FBlock_parallel_comp f5 f5_0 f5_1
      by (metis (no_types, lifting) Suc_1 Suc_eq_plus1 UnitDelay_def)
    (* (
        (
          (
            (
              Split2 (* door_closed (boolean, 1/10s) is split into two *) 
              \<parallel>\<^sub>B
              Id (* door_open_time: double *)
            ) ;; Router 3 [0,2,1]
          )
          \<parallel>\<^sub>B 
          post_mode
        )
        \<parallel>\<^sub>B
        (
           (UnitDelay 1.0 ;; LopNOT)
           \<parallel>\<^sub>B
           (UnitDelay 0) (* Delay2 *)
        )
      )
    *)
    let ?f6_f = "(\<lambda>x n. [hd(x n), hd(tl(x n)), hd(x n), 
            if (n > 0 \<and> (x (n-1))!2 = 4) then 1::real else 0,
            if (x n)!2 = 8 then 1 else 0,
            (if n = 0 then 0 else (if (x (n - 1))!3 = 0 then 1 else 0)), 
            if n = 0 then 0 else (x (n - 1))!4])"
    let ?f6 = "FBlock (\<lambda>x n. True) 5 7 ?f6_f"
    have f6: "((((
            Split2 (* door_closed (boolean, 1/10s) is split into two *) 
            \<parallel>\<^sub>B
            Id (* door_open_time: double *)
            ) ;; Router 3 [0,2,1])
            \<parallel>\<^sub>B 
            post_mode
          )
          \<parallel>\<^sub>B
          (
             (UnitDelay 1.0 ;; LopNOT)
             \<parallel>\<^sub>B
             (UnitDelay 0) (* Delay2 *)
          ))
      = ?f3 \<parallel>\<^sub>B ?f5"
      by (smt Suc3_eq_add_3 Suc_eq_plus1 add_2_eq_Suc eval_nat_numeral(3) f1 f1_0 f2_0 f2_1 f3_0 
          f3_1 f4 f4_0 f5_0 f5_1 numeral_Bit0 post_mode_simp)
    then have f6_0: "... = FBlock (\<lambda>x n. True) (3 + 2) (5 + 2) 
        (\<lambda>x n. (((?f3_f \<circ> (\<lambda>xx nn. take 3 (xx nn))) x n) @ 
                ((?f5_f \<circ> (\<lambda>xx nn. drop 3 (xx nn)))) x n))"
      using simblock_f3 simblock_f5 FBlock_parallel_comp by (simp)
    then have f6_1: "... = FBlock (\<lambda>x n. True) (3 + 2) (5 + 2) ?f6_f"
      proof -
        show ?thesis
          apply (simp add: FBlock_def)
          apply (rel_simp)
          apply (rule conjI, clarify, rule iffI)
          apply (clarify)
          defer
          apply (clarify)
          defer
          apply (clarify, rule iffI)
          apply (clarify)
          defer 
          apply (clarify)
          defer
          proof -
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::nat
            assume a1: "\<forall>x. (x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (take 3 (inouts\<^sub>v 0)), hd (tl (take 3 (inouts\<^sub>v 0))), hd (take 3 (inouts\<^sub>v 0)), 0, 1, 0, 0] =
              inouts\<^sub>v' 0) \<and>
             (0 < x \<longrightarrow>
              (hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x))))"
            from a1 have len_5: "\<forall>x. length(inouts\<^sub>v x) = 5"
              by (metis neq0_conv)
            have hd_take_3: "hd (take 3 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_5 by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
            have hd_tl_take_3: "hd (tl (take 3 (inouts\<^sub>v x))) = hd (tl (inouts\<^sub>v x))"
              using len_5 by (simp add: hd_tl_take_m)
            have hd_drop_3: "hd (drop 3 (inouts\<^sub>v x)) = inouts\<^sub>v x!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_drop_3': "hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = inouts\<^sub>v (x - Suc 0)!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_tl_drop_3: "hd (tl (drop 3 (inouts\<^sub>v x))) = inouts\<^sub>v x!(4)"
              using len_5 by (simp add: hd_drop_conv_nth nth_tl tl_drop)
            have hd_tl_drop_3': "hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0)))) = inouts\<^sub>v (x - Suc 0)!(4)"
              using len_5
              by (metis drop_Suc eval_nat_numeral(2) eval_nat_numeral(3) hd_drop_conv_nth lessI 
                  semiring_norm(26) semiring_norm(27) tl_drop)
            show "(x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 1, 0, 0] = inouts\<^sub>v' 0) \<and>
             (0 < x \<longrightarrow>
              (inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))))"
              using a1 hd_take_3 hd_tl_take_3 hd_drop_3' hd_tl_drop_3' by (smt )
          next
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::nat
            assume a1: "\<forall>x. (x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 1, 0, 0] = inouts\<^sub>v' 0) \<and>
             (0 < x \<longrightarrow>
              (inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))))"
            from a1 have len_5: "\<forall>x. length(inouts\<^sub>v x) = 5"
              by (metis neq0_conv)
            have hd_take_3: "hd (take 3 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_5 by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
            have hd_tl_take_3: "hd (tl (take 3 (inouts\<^sub>v x))) = hd (tl (inouts\<^sub>v x))"
              using len_5 by (simp add: hd_tl_take_m)
            have hd_drop_3: "hd (drop 3 (inouts\<^sub>v x)) = inouts\<^sub>v x!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_drop_3': "hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = inouts\<^sub>v (x - Suc 0)!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_tl_drop_3: "hd (tl (drop 3 (inouts\<^sub>v x))) = inouts\<^sub>v x!(4)"
              using len_5 by (simp add: hd_drop_conv_nth nth_tl tl_drop)
            have hd_tl_drop_3': "hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0)))) = inouts\<^sub>v (x - Suc 0)!(4)"
              using len_5
              by (metis drop_Suc eval_nat_numeral(2) eval_nat_numeral(3) hd_drop_conv_nth lessI 
                  semiring_norm(26) semiring_norm(27) tl_drop)
            show "(x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (take 3 (inouts\<^sub>v 0)), hd (tl (take 3 (inouts\<^sub>v 0))), hd (take 3 (inouts\<^sub>v 0)), 0, 1, 0, 0] =
              inouts\<^sub>v' 0) \<and>
             (0 < x \<longrightarrow>
              (hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x))))"
              using a1 hd_take_3 hd_tl_take_3 hd_drop_3' hd_tl_drop_3' by (smt )
          next
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::nat
            assume a1: "\<forall>x. (x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (take 3 (inouts\<^sub>v 0)), hd (tl (take 3 (inouts\<^sub>v 0))), hd (take 3 (inouts\<^sub>v 0)), 0, 0, 0, 0] =
              inouts\<^sub>v' 0 \<and>
              (\<not> inouts\<^sub>v 0!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 7 \<and>
               [hd (take 3 (inouts\<^sub>v 0)), hd (tl (take 3 (inouts\<^sub>v 0))), hd (take 3 (inouts\<^sub>v 0)), 0, 0, 0, 0] =
               inouts\<^sub>v' 0)) \<and>
             (0 < x \<longrightarrow>
              (hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x))))"
            from a1 have len_5: "\<forall>x. length(inouts\<^sub>v x) = 5"
              by (metis neq0_conv)
            have hd_take_3: "hd (take 3 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_5 by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
            have hd_tl_take_3: "hd (tl (take 3 (inouts\<^sub>v x))) = hd (tl (inouts\<^sub>v x))"
              using len_5 by (simp add: hd_tl_take_m)
            have hd_drop_3: "hd (drop 3 (inouts\<^sub>v x)) = inouts\<^sub>v x!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_drop_3': "hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = inouts\<^sub>v (x - Suc 0)!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_tl_drop_3: "hd (tl (drop 3 (inouts\<^sub>v x))) = inouts\<^sub>v x!(4)"
              using len_5 by (simp add: hd_drop_conv_nth nth_tl tl_drop)
            have hd_tl_drop_3': "hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0)))) = inouts\<^sub>v (x - Suc 0)!(4)"
              using len_5
              by (metis drop_Suc eval_nat_numeral(2) eval_nat_numeral(3) hd_drop_conv_nth lessI 
                  semiring_norm(26) semiring_norm(27) tl_drop)
            show "(x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0, 0, 0] = inouts\<^sub>v' 0 \<and>
              (\<not> inouts\<^sub>v 0!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 7 \<and>
               [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0, 0, 0] = inouts\<^sub>v' 0)) \<and>
             (0 < x \<longrightarrow>
              (inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))))"
              using a1 hd_take_3 hd_tl_take_3 hd_drop_3' hd_tl_drop_3' by (smt )
          next
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::nat
            assume a1: "\<forall>x. (x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0, 0, 0] = inouts\<^sub>v' 0 \<and>
              (\<not> inouts\<^sub>v 0!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 7 \<and>
               [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0, 0, 0] = inouts\<^sub>v' 0)) \<and>
             (0 < x \<longrightarrow>
              (inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))))"
            from a1 have len_5: "\<forall>x. length(inouts\<^sub>v x) = 5"
              by (metis neq0_conv)
            have hd_take_3: "hd (take 3 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_5 by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
            have hd_tl_take_3: "hd (tl (take 3 (inouts\<^sub>v x))) = hd (tl (inouts\<^sub>v x))"
              using len_5 by (simp add: hd_tl_take_m)
            have hd_drop_3: "hd (drop 3 (inouts\<^sub>v x)) = inouts\<^sub>v x!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_drop_3': "hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = inouts\<^sub>v (x - Suc 0)!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_tl_drop_3: "hd (tl (drop 3 (inouts\<^sub>v x))) = inouts\<^sub>v x!(4)"
              using len_5 by (simp add: hd_drop_conv_nth nth_tl tl_drop)
            have hd_tl_drop_3': "hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0)))) = inouts\<^sub>v (x - Suc 0)!(4)"
              using len_5
              by (metis drop_Suc eval_nat_numeral(2) eval_nat_numeral(3) hd_drop_conv_nth lessI 
                  semiring_norm(26) semiring_norm(27) tl_drop)
            show "(x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (take 3 (inouts\<^sub>v 0)), hd (tl (take 3 (inouts\<^sub>v 0))), hd (take 3 (inouts\<^sub>v 0)), 0, 0, 0, 0] =
              inouts\<^sub>v' 0 \<and>
              (\<not> inouts\<^sub>v 0!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 7 \<and>
               [hd (take 3 (inouts\<^sub>v 0)), hd (tl (take 3 (inouts\<^sub>v 0))), hd (take 3 (inouts\<^sub>v 0)), 0, 0, 0, 0] =
               inouts\<^sub>v' 0)) \<and>
             (0 < x \<longrightarrow>
              (hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)))) "
              using a1 hd_take_3 hd_tl_take_3 hd_drop_3' hd_tl_drop_3' by (smt )
          qed
      qed
    then have f6_2: "... = ?f6"
      by (smt Suc_eq_plus1 add_Suc_right numeral_Bit1 numeral_One one_add_one)
    have simblock_f6: "SimBlock 5 7 ?f6"
      using simblock_f3 simblock_f5 SimBlock_FBlock_parallel_comp 
      by (metis (no_types, lifting) Suc_1 Suc_eq_plus1 Suc_numeral add_numeral_left f6_0 f6_1 
          numeral_Bit1 numeral_One)
    (* Compositional Reasoning *)
    have ref_f6: "((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. ((hd(x n) = 0 \<or> hd(x n) = 1)))\<guillemotright> 
        (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred) 
      \<turnstile>\<^sub>n
      ((\<^bold>\<forall> n::nat \<bullet> 
        ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>5\<guillemotright>) \<and>
        ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>7\<guillemotright>) \<and>
        (head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) \<and> 
        (head\<^sub>u(tail\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u head\<^sub>u(tail\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a))))
      )) \<sqsubseteq> post_landing_finalize_part1"
      proof -
        have 1: "((\<^bold>\<forall> n::nat \<bullet> (
          \<guillemotleft>(\<lambda>x n. ((hd(x n) = 0 \<or> hd(x n) = 1)))\<guillemotright> 
            (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred) 
          \<turnstile>\<^sub>n
          ((\<^bold>\<forall> n::nat \<bullet> 
            ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>5\<guillemotright>) \<and>
            ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>7\<guillemotright>) \<and>
            (head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) \<and> 
            (head\<^sub>u(tail\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u head\<^sub>u(tail\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a))))
          )) \<sqsubseteq> ?f6"
          apply (simp add: FBlock_def)
          apply (rule ndesign_refine_intro)
          apply simp
          apply (rel_simp)
          apply (rule conjI, clarify)
          apply (metis gr_zeroI list.sel(1) list.sel(3))
          apply (clarify)
          by (metis gr_zeroI list.sel(1) list.sel(3))
        show ?thesis
          using 1 f6 f6_0 f6_1 f6_2 by simp
      qed
    show ?thesis
      using f6 f6_0 f6_1 f6_2 simblock_f6 by simp
  qed

lemma post_landing_finalize_part1_simp:
  "post_landing_finalize_part1 = plf1_1"
  using post_landing_finalize_part1_simp_and_simblock by blast

lemma post_landing_finalize_part1_simblock:
  "SimBlock 5 7 plf1_1"
  using post_landing_finalize_part1_simp_and_simblock by blast

subsubsection {* @{text "post_landing_finalize_part2"} *}

subsubsection {* @{text "post_landing_finalize_part3"} *}
*)

lemma post_landing_finalize_1_simp_simblock:
  "post_landing_finalize_1 = plf_rise1shot_simp f\<^sub>D (4, 1) \<and> SimBlock 5 2 plf_rise1shot_simp"
  proof -
    (*
      (
        Split2 (* door_closed (boolean, 1/10s) is split into two *) 
        \<parallel>\<^sub>B
        Id (* door_open_time: double *)
      ) ;; Router 3 [0,2,1]
    *)
    let ?f1_f = "(\<lambda>x n. [hd(x n), hd(x n), hd(tl(x n))])"
    let ?f1 = "FBlock (\<lambda>x n. True) 2 3 ?f1_f"
    have f1: "Split2 (* door_closed (boolean, 1/10s) is split into two *) 
        \<parallel>\<^sub>B Id (* door_open_time: double *) 
      = FBlock (\<lambda>x n. True) (1+1) (2+1) 
        (\<lambda>x n. (((f_Split2 \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                ((f_Id \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)) "
      using SimBlock_Id SimBlock_Split2 FBlock_parallel_comp 
      by (simp add: Split2_def simu_contract_real.Id_def)
    then have f1_0: "... = ?f1"
      proof -
        have "\<forall>x n. ((\<lambda>x n. (((f_Split2 \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                ((f_Id \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)) x n)
          = (?f1_f x n)"
          using f_Id_def f_Split2_def by (simp add: drop_Suc hd_take_m)
        then show ?thesis
          apply (simp)
          by (simp add: numeral_2_eq_2)
      qed
    have simblock_f1: "SimBlock 2 3 (?f1)"
      using SimBlock_Id SimBlock_Split2 SimBlock_FBlock_parallel_comp 
      by (metis (no_types, lifting) One_nat_def Split2_def Suc_1 Suc_eq_plus1 f1 f1_0 
          numeral_3_eq_3 simu_contract_real.Id_def)
    (* (
        Split2 (* door_closed (boolean, 1/10s) is split into two *) 
        \<parallel>\<^sub>B
        Id (* door_open_time: double *)
      ) ;; Router 3 [0,2,1] 
    *)
    let ?f2_f = "(\<lambda>x n. [hd(x n), hd(tl(x n)), hd(x n)])"
    let ?f2 = "FBlock (\<lambda>x n. True) (2) (3) ?f2_f"
    have f2: "(Split2 \<parallel>\<^sub>B Id) ;; Router 3 [0,2,1] = ?f1 ;; Router 3 [0,2,1]"
      using f1 f1_0 by auto
    then have f2_0: "... = FBlock (\<lambda>x n. True) (2) (3) (f_Router [0,2,1] o ?f1_f)"
      using simblock_f1 Router_def SimBlock_Router FBlock_seq_comp by simp
    then have f2_1: "... = ?f2"
      proof -
        have "\<forall>x n. (f_Router [0,2,1] o ?f1_f) x n = ?f2_f x n"
          using f_Router_def by (simp)
        then show ?thesis
          by presburger
      qed
    have simblock_f2: "SimBlock 2 3 ?f2"
      using simblock_f1 SimBlock_Router SimBlock_FBlock_seq_comp
      by (metis (no_types, lifting) Router_def f2_0 f2_1 length_Cons list.size(3) numeral_3_eq_3)
    (* (
      (
        (
          Split2 (* door_closed (boolean, 1/10s) is split into two *) 
          \<parallel>\<^sub>B
          Id (* door_open_time: double *)
        ) ;; Router 3 [0,2,1]
      )
      \<parallel>\<^sub>B 
      post_mode
    ) *)
    let ?post_mode_f = 
      "(\<lambda>x n. (([if (n > 0 \<and> hd(x (n-1)) = 4) then 1::real else 0, if hd(x n) = 8 then 1 else 0])))"
    let ?post_mode = "(FBlock (\<lambda>x n. True) (1) (2) ?post_mode_f)"
    have simblock_post_mode: "SimBlock 1 2 (?post_mode)"
      apply (rule SimBlock_FBlock)
      apply (rule_tac x = "\<lambda>na. [4]" in exI)
      apply (rule_tac x = "\<lambda>na. [if na > 0 then 1 else 0, 0]" in exI)
      apply (simp add: f_blocks)
      by (simp add: f_blocks)
    let ?f3_f = "(\<lambda>x n. [hd(x n), hd(tl(x n)), hd(x n), 
            if (n > 0 \<and> (x (n-1))!2 = 4) then 1::real else 0,
            if (x n)!2 = 8 then 1 else 0])"
    let ?f3 = "FBlock (\<lambda>x n. True) 3 5 ?f3_f"
    have f3: "((( Split2 (* door_closed (boolean, 1/10s) is split into two *) 
                \<parallel>\<^sub>B
                Id (* door_open_time: double *)
              ) ;; Router 3 [0,2,1])
              \<parallel>\<^sub>B post_mode) = ?f2 \<parallel>\<^sub>B ?post_mode"
      using f2 f2_0 f2_1 post_mode_simp by auto
    then have f3_0: "... = FBlock (\<lambda>x n. True) (2+1) (3+2) 
        (\<lambda>x n. (((?f2_f \<circ> (\<lambda>xx nn. take 2 (xx nn))) x n) @ 
                ((?post_mode_f \<circ> (\<lambda>xx nn. drop 2 (xx nn)))) x n))"
      using simblock_post_mode simblock_f1 FBlock_parallel_comp simblock_f2 by blast
    then have f3_1: "... = FBlock (\<lambda>x n. True) (2+1) (3+2) ?f3_f"
      proof -
        show ?thesis
          apply (simp add: FBlock_def)
          apply (rel_simp)
          apply (rule conjI, clarify)
          apply (rule conjI, clarify)
          apply (rule iffI, clarify)
          defer
          apply (clarify)
          defer 
          apply (clarify, rule iffI, clarify)
          apply (metis hd_drop_conv_nth lessI numeral_2_eq_2 numeral_3_eq_3)
          apply (clarify)
          apply (simp add: hd_drop_conv_nth)
          apply (clarify, rule conjI, clarify)
          apply (rule iffI, clarify)
          apply (metis hd_drop_conv_nth lessI numeral_2_eq_2 numeral_3_eq_3)
          apply (clarify)
          apply (simp add: hd_drop_conv_nth)
          apply (clarify, rule iffI, clarify)
          defer
          apply (clarify)
          defer
          proof -
            fix ok\<^sub>v ok\<^sub>v'::bool and inouts\<^sub>v  inouts\<^sub>v'::"nat \<Rightarrow> real list" and x
            assume a1: "\<forall>x. (hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 1] =
               inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 1] =
               inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 1] =
               inouts\<^sub>v' x)) \<and>
             (\<not> hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 0] =
               inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 1] =
               inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 0] =
               inouts\<^sub>v' x))"
            from a1 have len_3: "\<forall>x. length(inouts\<^sub>v x) = 3"
              by (metis neq0_conv)
            have drop_2: "\<forall>x. (hd (drop 2 (inouts\<^sub>v' x)) = (inouts\<^sub>v' x)!2)"
              using len_3 hd_drop_m
              by (metis Suc_eq_plus1 Suc_le_eq a1 add_Suc_right add_diff_cancel_right' diff_le_self 
                  hd_drop_conv_nth neq0_conv one_plus_numeral one_plus_numeral_commute semiring_norm(2) 
                  semiring_norm(3) semiring_norm(4))
            have take_2: "\<forall>x. hd (take 2 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_3 hd_take_m by simp
            have take_tl_2: "\<forall>x. hd (tl (take 2 (inouts\<^sub>v x))) = hd(tl(inouts\<^sub>v x))"
              using len_3 hd_tl_take_m by simp
            show "(inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 1] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 1] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0] = inouts\<^sub>v' x))"
            using drop_2 take_2 take_tl_2
            by (metis One_nat_def Suc_1 a1 hd_drop_conv_nth len_3 lessI numeral_3_eq_3)
          next
            fix ok\<^sub>v ok\<^sub>v'::bool and inouts\<^sub>v  inouts\<^sub>v'::"nat \<Rightarrow> real list" and x
            assume a1: "\<forall>x. (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 1] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 1] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0] = inouts\<^sub>v' x))"
            from a1 have len_3: "\<forall>x. length(inouts\<^sub>v x) = 3"
              by (metis neq0_conv)
            have drop_2: "\<forall>x. (hd (drop 2 (inouts\<^sub>v' x)) = (inouts\<^sub>v' x)!2)"
              using len_3 hd_drop_m
              by (metis Suc_eq_plus1 Suc_le_eq a1 add_Suc_right add_diff_cancel_right' diff_le_self 
                  hd_drop_conv_nth neq0_conv one_plus_numeral one_plus_numeral_commute semiring_norm(2) 
                  semiring_norm(3) semiring_norm(4))
            have take_2: "\<forall>x. hd (take 2 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_3 hd_take_m by simp
            have take_tl_2: "\<forall>x. hd (tl (take 2 (inouts\<^sub>v x))) = hd(tl(inouts\<^sub>v x))"
              using len_3 hd_tl_take_m by simp
            show "(hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 1] =
               inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 1] =
               inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 1] =
               inouts\<^sub>v' x)) \<and>
             (\<not> hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 0] =
               inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 1] =
               inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and>
               [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 0] =
               inouts\<^sub>v' x))"
            using drop_2 take_2 take_tl_2
            by (metis One_nat_def Suc_1 a1 hd_drop_conv_nth len_3 lessI numeral_3_eq_3)
          next
            fix ok\<^sub>v ok\<^sub>v'::bool and inouts\<^sub>v  inouts\<^sub>v'::"nat \<Rightarrow> real list" and x::nat
            assume a1: "\<forall>x. (hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 1] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 0] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 0] = inouts\<^sub>v' x))"
            assume a2: "\<not> hd (drop 2 (inouts\<^sub>v 0)) = 8"
            assume a3: "\<not> inouts\<^sub>v 0!(2) = 8"
            from a1 have len_3: "\<forall>x. length(inouts\<^sub>v x) = 3"
              by (metis neq0_conv)
            have drop_2: "\<forall>x. (hd (drop 2 (inouts\<^sub>v' x)) = (inouts\<^sub>v' x)!2)"
              using len_3 hd_drop_m
              by (metis Suc_eq_plus1 Suc_le_eq a1 add_Suc_right add_diff_cancel_right' diff_le_self 
                  hd_drop_conv_nth neq0_conv one_plus_numeral one_plus_numeral_commute semiring_norm(2) 
                  semiring_norm(3) semiring_norm(4))
            have take_2: "\<forall>x. hd (take 2 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_3 hd_take_m by simp
            have take_tl_2: "\<forall>x. hd (tl (take 2 (inouts\<^sub>v x))) = hd(tl(inouts\<^sub>v x))"
              using len_3 hd_tl_take_m by simp
            show "(inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0] = inouts\<^sub>v' x))"
            using drop_2 take_2 take_tl_2
            by (metis One_nat_def Suc_1 a1 hd_drop_conv_nth len_3 lessI numeral_3_eq_3)
          next
            fix ok\<^sub>v ok\<^sub>v'::bool and inouts\<^sub>v  inouts\<^sub>v'::"nat \<Rightarrow> real list" and x
            assume a1: "\<forall>x. (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and> length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
              (0 < x \<and> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and> length(inouts\<^sub>v' 0) = 5 \<and> [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and> length(inouts\<^sub>v' x) = 5 \<and> [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0] = inouts\<^sub>v' x))"
            from a1 have len_3: "\<forall>x. length(inouts\<^sub>v x) = 3"
              by (metis neq0_conv)
            have drop_2: "\<forall>x. (hd (drop 2 (inouts\<^sub>v' x)) = (inouts\<^sub>v' x)!2)"
              using len_3 hd_drop_m
              by (metis Suc_eq_plus1 Suc_le_eq a1 add_Suc_right add_diff_cancel_right' diff_le_self 
                  hd_drop_conv_nth neq0_conv one_plus_numeral one_plus_numeral_commute semiring_norm(2) 
                  semiring_norm(3) semiring_norm(4))
            have take_2: "\<forall>x. hd (take 2 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_3 hd_take_m by simp
            have take_tl_2: "\<forall>x. hd (tl (take 2 (inouts\<^sub>v x))) = hd(tl(inouts\<^sub>v x))"
              using len_3 hd_tl_take_m by simp
            show "(hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 1] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> hd (drop 2 (inouts\<^sub>v x)) = 8 \<longrightarrow>
              (0 < x \<and> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 1, 0] = inouts\<^sub>v' x) \<and>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 3 \<and>
               length(inouts\<^sub>v' 0) = 5 \<and> [hd (take 2 (inouts\<^sub>v 0)), hd (tl (take 2 (inouts\<^sub>v 0))), hd (take 2 (inouts\<^sub>v 0)), 0, 0] = inouts\<^sub>v' 0) \<and>
              (\<not> hd (drop 2 (inouts\<^sub>v (x - Suc 0))) = 4 \<longrightarrow>
               length(inouts\<^sub>v x) = 3 \<and>
               length(inouts\<^sub>v' x) = 5 \<and> [hd (take 2 (inouts\<^sub>v x)), hd (tl (take 2 (inouts\<^sub>v x))), hd (take 2 (inouts\<^sub>v x)), 0, 0] = inouts\<^sub>v' x))"
            using drop_2 take_2 take_tl_2
            by (metis One_nat_def Suc_1 a1 hd_drop_conv_nth len_3 lessI numeral_3_eq_3)
          qed
      qed
    have simblock_f3: "SimBlock 3 5 (?f3)"
      using simblock_f2 simblock_post_mode SimBlock_FBlock_parallel_comp
      by (smt Suc_eq_plus1 add_Suc f3_0 f3_1 numeral_2_eq_2 numeral_3_eq_3 numeral_code(3))
    (* 
       (UnitDelay 1.0 ;; LopNOT)
    *)
    let ?f4_f = "(\<lambda>x n. [(if n = 0 then 0 else (if hd(x (n-1)) = 0 then 1 else 0))])"
    let ?f4 = "FBlock (\<lambda>x n. True) 1 1 ?f4_f"
    have f4: "(UnitDelay 1.0 ;; LopNOT) = FBlock (\<lambda>x n. True) 1 1 (f_LopNOT o f_UnitDelay 1.0)"
      using SimBlock_UnitDelay SimBlock_LopNOT FBlock_seq_comp by (simp add: LopNOT_def UnitDelay_def)
    then have f4_0: "... = FBlock (\<lambda>x n. True) 1 1 ?f4_f"
      proof -
        have "\<forall>x n. (f_LopNOT o f_UnitDelay 1.0) x n = ?f4_f x n"
          using f_LopNOT_def f_UnitDelay_def by simp
        then show ?thesis
          by presburger
      qed
    have simblock_f4: "SimBlock 1 1 ?f4"
      using SimBlock_UnitDelay SimBlock_LopNOT SimBlock_FBlock_seq_comp
      by (metis (no_types, lifting) LopNOT_def UnitDelay_def f4 f4_0)
    (* (UnitDelay 1.0 ;; LopNOT)
       \<parallel>\<^sub>B
       (UnitDelay 0) (* Delay2 *) *)
    let ?f5_f = "(\<lambda>x n. [(if n = 0 then 0 else (if hd(x (n-1)) = 0 then 1 else 0)), 
      if n = 0 then 0 else hd(tl(x (n - 1)))])"
    let ?f5 = "FBlock (\<lambda>x n. True) 2 2 ?f5_f"
    have f5: "((UnitDelay 1.0 ;; LopNOT)
             \<parallel>\<^sub>B
             (UnitDelay 0) (* Delay2 *))
      = ?f4 \<parallel>\<^sub>B (UnitDelay 0)"
      using f4 f4_0 by auto
    then have f5_0: "... = FBlock (\<lambda>x n. True) 2 2 
        (\<lambda>x n. (((?f4_f \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                ((f_UnitDelay 0 \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n))"
      using simblock_f4 SimBlock_UnitDelay FBlock_parallel_comp apply (simp add: UnitDelay_def)
      by (simp add: numeral_2_eq_2)
    then have f5_1: "... = ?f5"
      proof -
        have "\<forall>x n. (\<lambda>x n. (((?f4_f \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                ((f_UnitDelay 0 \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n))  x n
          = ?f5_f x n"
          using f_UnitDelay_def apply (simp)
          apply (rule allI)+
          apply (rule conjI, clarify)
          apply (simp add: drop_Suc hd_take_m)
          by (simp add: drop_Suc hd_take_m)
        then show ?thesis
          by presburger
      qed
    have simblock_f5: "SimBlock 2 2 ?f5"
      using simblock_f4 SimBlock_UnitDelay SimBlock_FBlock_parallel_comp f5 f5_0 f5_1
      by (metis (no_types, lifting) Suc_1 Suc_eq_plus1 UnitDelay_def)
    (* (
        (
          (
            (
              Split2 (* door_closed (boolean, 1/10s) is split into two *) 
              \<parallel>\<^sub>B
              Id (* door_open_time: double *)
            ) ;; Router 3 [0,2,1]
          )
          \<parallel>\<^sub>B 
          post_mode
        )
        \<parallel>\<^sub>B
        (
           (UnitDelay 1.0 ;; LopNOT)
           \<parallel>\<^sub>B
           (UnitDelay 0) (* Delay2 *)
        )
      )
    *)
    let ?f6_f = "(\<lambda>x n. [hd(x n), hd(tl(x n)), hd(x n), 
            if (n > 0 \<and> (x (n-1))!2 = 4) then 1::real else 0,
            if (x n)!2 = 8 then 1 else 0,
            (if n = 0 then 0 else (if (x (n - 1))!3 = 0 then 1 else 0)), 
            if n = 0 then 0 else (x (n - 1))!4])"
    let ?f6 = "FBlock (\<lambda>x n. True) 5 7 ?f6_f"
    have f6: "((((
            Split2 (* door_closed (boolean, 1/10s) is split into two *) 
            \<parallel>\<^sub>B
            Id (* door_open_time: double *)
            ) ;; Router 3 [0,2,1])
            \<parallel>\<^sub>B 
            post_mode
          )
          \<parallel>\<^sub>B
          (
             (UnitDelay 1.0 ;; LopNOT)
             \<parallel>\<^sub>B
             (UnitDelay 0) (* Delay2 *)
          ))
      = ?f3 \<parallel>\<^sub>B ?f5"
      by (smt Suc3_eq_add_3 Suc_eq_plus1 add_2_eq_Suc eval_nat_numeral(3) f1 f1_0 f2_0 f2_1 f3_0 
          f3_1 f4 f4_0 f5_0 f5_1 numeral_Bit0 post_mode_simp)
    then have f6_0: "... = FBlock (\<lambda>x n. True) (3 + 2) (5 + 2) 
        (\<lambda>x n. (((?f3_f \<circ> (\<lambda>xx nn. take 3 (xx nn))) x n) @ 
                ((?f5_f \<circ> (\<lambda>xx nn. drop 3 (xx nn)))) x n))"
      using simblock_f3 simblock_f5 FBlock_parallel_comp by (simp)
    then have f6_1: "... = FBlock (\<lambda>x n. True) (3 + 2) (5 + 2) ?f6_f"
      proof -
        show ?thesis
          apply (simp add: FBlock_def)
          apply (rel_simp)
          apply (rule conjI, clarify, rule iffI)
          apply (clarify)
          defer
          apply (clarify)
          defer
          apply (clarify, rule iffI)
          apply (clarify)
          defer 
          apply (clarify)
          defer
          proof -
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::nat
            assume a1: "\<forall>x. (x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (take 3 (inouts\<^sub>v 0)), hd (tl (take 3 (inouts\<^sub>v 0))), hd (take 3 (inouts\<^sub>v 0)), 0, 1, 0, 0] =
              inouts\<^sub>v' 0) \<and>
             (0 < x \<longrightarrow>
              (hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x))))"
            from a1 have len_5: "\<forall>x. length(inouts\<^sub>v x) = 5"
              by (metis neq0_conv)
            have hd_take_3: "hd (take 3 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_5 by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
            have hd_tl_take_3: "hd (tl (take 3 (inouts\<^sub>v x))) = hd (tl (inouts\<^sub>v x))"
              using len_5 by (simp add: hd_tl_take_m)
            have hd_drop_3: "hd (drop 3 (inouts\<^sub>v x)) = inouts\<^sub>v x!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_drop_3': "hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = inouts\<^sub>v (x - Suc 0)!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_tl_drop_3: "hd (tl (drop 3 (inouts\<^sub>v x))) = inouts\<^sub>v x!(4)"
              using len_5 by (simp add: hd_drop_conv_nth nth_tl tl_drop)
            have hd_tl_drop_3': "hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0)))) = inouts\<^sub>v (x - Suc 0)!(4)"
              using len_5
              by (metis drop_Suc eval_nat_numeral(2) eval_nat_numeral(3) hd_drop_conv_nth lessI 
                  semiring_norm(26) semiring_norm(27) tl_drop)
            show "(x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 1, 0, 0] = inouts\<^sub>v' 0) \<and>
             (0 < x \<longrightarrow>
              (inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))))"
              using a1 hd_take_3 hd_tl_take_3 hd_drop_3' hd_tl_drop_3' by (smt )
          next
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::nat
            assume a1: "\<forall>x. (x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 1, 0, 0] = inouts\<^sub>v' 0) \<and>
             (0 < x \<longrightarrow>
              (inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))))"
            from a1 have len_5: "\<forall>x. length(inouts\<^sub>v x) = 5"
              by (metis neq0_conv)
            have hd_take_3: "hd (take 3 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_5 by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
            have hd_tl_take_3: "hd (tl (take 3 (inouts\<^sub>v x))) = hd (tl (inouts\<^sub>v x))"
              using len_5 by (simp add: hd_tl_take_m)
            have hd_drop_3: "hd (drop 3 (inouts\<^sub>v x)) = inouts\<^sub>v x!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_drop_3': "hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = inouts\<^sub>v (x - Suc 0)!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_tl_drop_3: "hd (tl (drop 3 (inouts\<^sub>v x))) = inouts\<^sub>v x!(4)"
              using len_5 by (simp add: hd_drop_conv_nth nth_tl tl_drop)
            have hd_tl_drop_3': "hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0)))) = inouts\<^sub>v (x - Suc 0)!(4)"
              using len_5
              by (metis drop_Suc eval_nat_numeral(2) eval_nat_numeral(3) hd_drop_conv_nth lessI 
                  semiring_norm(26) semiring_norm(27) tl_drop)
            show "(x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (take 3 (inouts\<^sub>v 0)), hd (tl (take 3 (inouts\<^sub>v 0))), hd (take 3 (inouts\<^sub>v 0)), 0, 1, 0, 0] =
              inouts\<^sub>v' 0) \<and>
             (0 < x \<longrightarrow>
              (hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x))))"
              using a1 hd_take_3 hd_tl_take_3 hd_drop_3' hd_tl_drop_3' by (smt )
          next
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::nat
            assume a1: "\<forall>x. (x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (take 3 (inouts\<^sub>v 0)), hd (tl (take 3 (inouts\<^sub>v 0))), hd (take 3 (inouts\<^sub>v 0)), 0, 0, 0, 0] =
              inouts\<^sub>v' 0 \<and>
              (\<not> inouts\<^sub>v 0!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 7 \<and>
               [hd (take 3 (inouts\<^sub>v 0)), hd (tl (take 3 (inouts\<^sub>v 0))), hd (take 3 (inouts\<^sub>v 0)), 0, 0, 0, 0] =
               inouts\<^sub>v' 0)) \<and>
             (0 < x \<longrightarrow>
              (hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x))))"
            from a1 have len_5: "\<forall>x. length(inouts\<^sub>v x) = 5"
              by (metis neq0_conv)
            have hd_take_3: "hd (take 3 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_5 by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
            have hd_tl_take_3: "hd (tl (take 3 (inouts\<^sub>v x))) = hd (tl (inouts\<^sub>v x))"
              using len_5 by (simp add: hd_tl_take_m)
            have hd_drop_3: "hd (drop 3 (inouts\<^sub>v x)) = inouts\<^sub>v x!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_drop_3': "hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = inouts\<^sub>v (x - Suc 0)!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_tl_drop_3: "hd (tl (drop 3 (inouts\<^sub>v x))) = inouts\<^sub>v x!(4)"
              using len_5 by (simp add: hd_drop_conv_nth nth_tl tl_drop)
            have hd_tl_drop_3': "hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0)))) = inouts\<^sub>v (x - Suc 0)!(4)"
              using len_5
              by (metis drop_Suc eval_nat_numeral(2) eval_nat_numeral(3) hd_drop_conv_nth lessI 
                  semiring_norm(26) semiring_norm(27) tl_drop)
            show "(x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0, 0, 0] = inouts\<^sub>v' 0 \<and>
              (\<not> inouts\<^sub>v 0!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 7 \<and>
               [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0, 0, 0] = inouts\<^sub>v' 0)) \<and>
             (0 < x \<longrightarrow>
              (inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))))"
              using a1 hd_take_3 hd_tl_take_3 hd_drop_3' hd_tl_drop_3' by (smt )
          next
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::nat
            assume a1: "\<forall>x. (x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0, 0, 0] = inouts\<^sub>v' 0 \<and>
              (\<not> inouts\<^sub>v 0!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 7 \<and>
               [hd (inouts\<^sub>v 0), hd (tl (inouts\<^sub>v 0)), hd (inouts\<^sub>v 0), 0, 0, 0, 0] = inouts\<^sub>v' 0)) \<and>
             (0 < x \<longrightarrow>
              (inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 1, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> inouts\<^sub>v (x - Suc 0)!(3) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 1, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 1, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (inouts\<^sub>v x), hd (tl (inouts\<^sub>v x)), hd (inouts\<^sub>v x), 0, 0, 0, inouts\<^sub>v (x - Suc 0)!(4)] =
                 inouts\<^sub>v' x))))"
            from a1 have len_5: "\<forall>x. length(inouts\<^sub>v x) = 5"
              by (metis neq0_conv)
            have hd_take_3: "hd (take 3 (inouts\<^sub>v x)) = hd(inouts\<^sub>v x)"
              using len_5 by (metis append_take_drop_id hd_append2 take_eq_Nil zero_neq_numeral)
            have hd_tl_take_3: "hd (tl (take 3 (inouts\<^sub>v x))) = hd (tl (inouts\<^sub>v x))"
              using len_5 by (simp add: hd_tl_take_m)
            have hd_drop_3: "hd (drop 3 (inouts\<^sub>v x)) = inouts\<^sub>v x!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_drop_3': "hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = inouts\<^sub>v (x - Suc 0)!(3)"
              using len_5 by (simp add: hd_drop_conv_nth)
            have hd_tl_drop_3: "hd (tl (drop 3 (inouts\<^sub>v x))) = inouts\<^sub>v x!(4)"
              using len_5 by (simp add: hd_drop_conv_nth nth_tl tl_drop)
            have hd_tl_drop_3': "hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0)))) = inouts\<^sub>v (x - Suc 0)!(4)"
              using len_5
              by (metis drop_Suc eval_nat_numeral(2) eval_nat_numeral(3) hd_drop_conv_nth lessI 
                  semiring_norm(26) semiring_norm(27) tl_drop)
            show "(x = 0 \<longrightarrow>
              length(inouts\<^sub>v 0) = 5 \<and>
              length(inouts\<^sub>v' 0) = 7 \<and>
              [hd (take 3 (inouts\<^sub>v 0)), hd (tl (take 3 (inouts\<^sub>v 0))), hd (take 3 (inouts\<^sub>v 0)), 0, 0, 0, 0] =
              inouts\<^sub>v' 0 \<and>
              (\<not> inouts\<^sub>v 0!(2) = 4 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 7 \<and>
               [hd (take 3 (inouts\<^sub>v 0)), hd (tl (take 3 (inouts\<^sub>v 0))), hd (take 3 (inouts\<^sub>v 0)), 0, 0, 0, 0] =
               inouts\<^sub>v' 0)) \<and>
             (0 < x \<longrightarrow>
              (hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 1,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x))) \<and>
              (\<not> hd (drop 3 (inouts\<^sub>v (x - Suc 0))) = 0 \<longrightarrow>
               (inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 1, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)) \<and>
               (\<not> inouts\<^sub>v x!(2) = 8 \<longrightarrow>
                (inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 1, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x) \<and>
                (\<not> inouts\<^sub>v (x - Suc 0)!(2) = 4 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 7 \<and>
                 [hd (take 3 (inouts\<^sub>v x)), hd (tl (take 3 (inouts\<^sub>v x))), hd (take 3 (inouts\<^sub>v x)), 0, 0, 0,
                  hd (tl (drop 3 (inouts\<^sub>v (x - Suc 0))))] =
                 inouts\<^sub>v' x)))) "
              using a1 hd_take_3 hd_tl_take_3 hd_drop_3' hd_tl_drop_3' by (smt )
          qed
      qed
    then have f6_2: "... = ?f6"
      by (smt Suc_eq_plus1 add_Suc_right numeral_Bit1 numeral_One one_add_one)
    have simblock_f6: "SimBlock 5 7 ?f6"
      using simblock_f3 simblock_f5 SimBlock_FBlock_parallel_comp 
      by (metis (no_types, lifting) Suc_1 Suc_eq_plus1 Suc_numeral add_numeral_left f6_0 f6_1 
          numeral_Bit1 numeral_One)
    (* Compositional Reasoning *)
    have ref_f6: "((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. ((hd(x n) = 0 \<or> hd(x n) = 1)))\<guillemotright> 
        (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred) 
      \<turnstile>\<^sub>n
      ((\<^bold>\<forall> n::nat \<bullet> 
        ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>5\<guillemotright>) \<and>
        ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>7\<guillemotright>) \<and>
        (head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) \<and> 
        (head\<^sub>u(tail\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u head\<^sub>u(tail\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a))))
      )) \<sqsubseteq> post_landing_finalize_part1"
      proof -
        have 1: "((\<^bold>\<forall> n::nat \<bullet> (
          \<guillemotleft>(\<lambda>x n. ((hd(x n) = 0 \<or> hd(x n) = 1)))\<guillemotright> 
            (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred) 
          \<turnstile>\<^sub>n
          ((\<^bold>\<forall> n::nat \<bullet> 
            ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>5\<guillemotright>) \<and>
            ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>7\<guillemotright>) \<and>
            (head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) \<and> 
            (head\<^sub>u(tail\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u head\<^sub>u(tail\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a))))
          )) \<sqsubseteq> ?f6"
          apply (simp add: FBlock_def)
          apply (rule ndesign_refine_intro)
          apply simp
          apply (rel_simp)
          apply (rule conjI, clarify)
          apply (metis gr_zeroI list.sel(1) list.sel(3))
          apply (clarify)
          by (metis gr_zeroI list.sel(1) list.sel(3))
        show ?thesis
          using 1 f6 f6_0 f6_1 f6_2 by simp
      qed
    (* (((
         (LopNOT)
         \<parallel>\<^sub>B
         (Id) (* door_open_time: double *)
      ) ;; variableTimer
    )
    \<parallel>\<^sub>B
    ((   (LopAND 3)
         \<parallel>\<^sub>B
         (LopOR 2)
      ) ;; latch)) *)
    (* ( (LopNOT)
         \<parallel>\<^sub>B
         (Id) (* door_open_time: double *))
    *)
    let ?f7_f = "(\<lambda>x n. [if hd(x n) = 0 then 1 else 0, hd(tl(x n))])"
    let ?f7 = "FBlock (\<lambda>x n. True) 2 2 ?f7_f"
    have f7: "((LopNOT)  \<parallel>\<^sub>B (Id) (* door_open_time: double *)) = 
      FBlock (\<lambda>x n. True) (1+1) (1+1) 
        (\<lambda>x n. (((f_LopNOT \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ ((f_Id \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n))"
      using SimBlock_LopNOT SimBlock_Id FBlock_parallel_comp 
      by (simp add: LopNOT_def simu_contract_real.Id_def)
    then have f7_0: "... = FBlock (\<lambda>x n. True) 2 2 ?f7_f"
      proof -
        have "\<forall>x n. (\<lambda>x n. (((f_LopNOT \<circ> (\<lambda>xx nn. take 1 (xx nn))) x n) @ 
                    ((f_Id \<circ> (\<lambda>xx nn. drop 1 (xx nn)))) x n)) x n = ?f7_f x n"
          by (simp add: drop_Suc f_Id_def f_LopNOT_def hd_take_m)
        then show ?thesis
          by (simp add: numeral_2_eq_2 )
      qed
    have simblock_f7: "SimBlock 2 2 (?f7)"
      using SimBlock_LopNOT SimBlock_Id SimBlock_FBlock_parallel_comp
      by (metis (no_types, lifting) LopNOT_def f7 f7_0 one_add_one simu_contract_real.Id_def)

    (* (((LopNOT) \<parallel>\<^sub>B (Id) (* door_open_time: double *)) ;; variableTimer )*)
    let ?f8_f = "(\<lambda>x na. [if (if 1 \<le> (if hd(x na) = 0 then 1::real else 0) * 2
                   then (if na = 0 then 0
                   else min (vT_fd_sol_1
                           (\<lambda>n1. (\<lambda>na. real_of_int
                                  (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) n1)
                           (\<lambda>n1. (if hd(x n1) = 0 then 1::real else 0)) (na - 1))
                      ((\<lambda>na. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>))))
                            (na - 1))) + 1
                  else 0) > (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) 
          then 1 else 0])"
    let ?f8_f' = "(\<lambda>x na. [if (if hd(x na) = 0
                   then (if na = 0 then 0
                         else min (vT_fd_sol_1
                                 (\<lambda>n1. (\<lambda>na. real_of_int
                                        (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) n1)
                                 (\<lambda>n1. (if hd(x n1) = 0 then 1::real else 0)) (na - 1))
                            ((\<lambda>na. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>))))
                                  (na - 1))) + 1
                    else 0) > (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) 
          then 1 else 0])"
    let ?f8 = "FBlock (\<lambda>x n. True) 2 1 ?f8_f'"
    have f8: "((LopNOT) \<parallel>\<^sub>B (Id) (* door_open_time: double *)) ;; variableTimer
      = ?f7 ;; variableTimer_simp_pat"
      using variableTimer_simp f7 f7_0 by auto
    then have f8_0: "... = FBlock (\<lambda>x n. True) 2 1 (variableTimer_simp_pat_f o ?f7_f)"
      using simblock_f7 SimBlock_variableTimer_simp FBlock_seq_comp by blast
    then have f8_1: "... = ?f8"
      proof -
        show ?thesis
          apply (simp add: FBlock_def)
          apply (rel_simp)
          apply (rule iffI)
          apply (clarify)
          defer
          apply (clarify)
          defer
          proof -
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::nat
            assume a1: "\<forall>x. (x = 0 \<longrightarrow>
              (hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v 0))) 0\<rceil>)) < 1 \<longrightarrow>
                length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [1] = inouts\<^sub>v' 0) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v 0))) 0\<rceil>)) < 1 \<longrightarrow>
                length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [0] = inouts\<^sub>v' 0)) \<and>
              (\<not> hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v 0))) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [1] = inouts\<^sub>v' 0) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v 0))) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [0] = inouts\<^sub>v' 0))) \<and>
             (0 < x \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v x))) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v n1))) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v (x - Suc 0)))) 0\<rceil>)))) +
                  1 \<longrightarrow>
                length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [1] = inouts\<^sub>v' x) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v x))) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v n1))) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int
                        (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v (x - Suc 0)))) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [0] = inouts\<^sub>v' x)) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v x))) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [1] = inouts\<^sub>v' x) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v x))) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [0] = inouts\<^sub>v' x)))"
            from a1 have len_2: "\<forall>x. length(inouts\<^sub>v x) = 2"
              by (metis (no_types, lifting) gr_zeroI)
            have hd_tl_2: "hd (tl (inouts\<^sub>v x)) = inouts\<^sub>v x!(Suc 0)"
              using len_2 
              by (metis Suc_1 diff_Suc_1 hd_conv_nth length_tl less_numeral_extra(1) list.size(3) 
                nth_tl zero_neq_one)
            have hd_tl_2': "\<forall>x. hd (tl (inouts\<^sub>v x)) = inouts\<^sub>v x!(Suc 0)"
              using len_2 
              by (metis Suc_1 diff_Suc_1 hd_conv_nth length_tl less_numeral_extra(1) list.size(3) nth_tl zero_neq_one)
            have hd_tl_2'': "(hd (tl (inouts\<^sub>v (x - Suc 0)))) = (inouts\<^sub>v (x - Suc 0)!(Suc 0))"
              using len_2 using hd_tl_2' by blast
            from a1 have a1': "\<forall>x. (x = 0 \<longrightarrow>
                (hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
                 (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
                  length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [1] = inouts\<^sub>v' 0) \<and>
                 (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
                  length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [0] = inouts\<^sub>v' 0)) \<and>
                (\<not> hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
                 (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                  length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [1] = inouts\<^sub>v' 0) \<and>
                 (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                  length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [0] = inouts\<^sub>v' 0))) \<and>
               (0 < x \<longrightarrow>
                (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                  < min (vT_fd_sol_1
                          (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                          (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                     (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                    1 \<longrightarrow>
                  length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [1] = inouts\<^sub>v' x) \<and>
                 (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                     < min (vT_fd_sol_1
                             (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                             (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                        (real_of_int
                          (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                       1 \<longrightarrow>
                  length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [0] = inouts\<^sub>v' x)) \<and>
                (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                 (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [1] = inouts\<^sub>v' x) \<and>
                 (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [0] = inouts\<^sub>v' x)))"
              using hd_tl_2' by presburger
            show "(x = 0 \<longrightarrow>
              (hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
                length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [1] = inouts\<^sub>v' 0) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
                length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [0] = inouts\<^sub>v' 0)) \<and>
              (\<not> hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [1] = inouts\<^sub>v' 0) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [0] = inouts\<^sub>v' 0))) \<and>
             (0 < x \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [1] = inouts\<^sub>v' x) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [0] = inouts\<^sub>v' x)) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [1] = inouts\<^sub>v' x) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [0] = inouts\<^sub>v' x)))"
              using a1' by blast
            next
              fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::nat
              assume a1: "\<forall>x. (x = 0 \<longrightarrow>
                (hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
                 (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
                  length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [1] = inouts\<^sub>v' 0) \<and>
                 (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
                  length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [0] = inouts\<^sub>v' 0)) \<and>
                (\<not> hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
                 (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                  length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [1] = inouts\<^sub>v' 0) \<and>
                 (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                  length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [0] = inouts\<^sub>v' 0))) \<and>
               (0 < x \<longrightarrow>
                (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                  < min (vT_fd_sol_1 (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                          (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                     (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                    1 \<longrightarrow>
                  length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [1] = inouts\<^sub>v' x) \<and>
                 (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                     < min (vT_fd_sol_1 (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                             (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                        (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                       1 \<longrightarrow>
                  length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [0] = inouts\<^sub>v' x)) \<and>
                (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                 (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [1] = inouts\<^sub>v' x) \<and>
                 (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [0] = inouts\<^sub>v' x)))"
            from a1 have len_2: "\<forall>x. length(inouts\<^sub>v x) = 2"
              by (metis (no_types, lifting) gr_zeroI)
            have hd_tl_2: "hd (tl (inouts\<^sub>v x)) = inouts\<^sub>v x!(Suc 0)"
              using len_2 
              by (metis Suc_1 diff_Suc_1 hd_conv_nth length_tl less_numeral_extra(1) list.size(3) 
                nth_tl zero_neq_one)
            have hd_tl_2': "\<forall>x. hd (tl (inouts\<^sub>v x)) = inouts\<^sub>v x!(Suc 0)"
              using len_2 
              by (metis Suc_1 diff_Suc_1 hd_conv_nth length_tl less_numeral_extra(1) list.size(3) nth_tl zero_neq_one)
            have hd_tl_2'': "(hd (tl (inouts\<^sub>v (x - Suc 0)))) = (inouts\<^sub>v (x - Suc 0)!(Suc 0))"
              using len_2 using hd_tl_2' by blast
            from a1 have a1': "\<forall>x. (x = 0 \<longrightarrow>
                (hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
                 (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v 0))) 0\<rceil>)) < 1 \<longrightarrow>
                  length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [1] = inouts\<^sub>v' 0) \<and>
                 (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v 0))) 0\<rceil>)) < 1 \<longrightarrow>
                  length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [0] = inouts\<^sub>v' 0)) \<and>
                (\<not> hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
                 (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v 0))) 0\<rceil>)) < 0 \<longrightarrow>
                  length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [1] = inouts\<^sub>v' 0) \<and>
                 (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v 0))) 0\<rceil>)) < 0 \<longrightarrow>
                  length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [0] = inouts\<^sub>v' 0))) \<and>
               (0 < x \<longrightarrow>
                (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v x))) 0\<rceil>)))
                  < min (vT_fd_sol_1 (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v n1))) 0\<rceil>))))
                          (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                     (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v (x - Suc 0)))) 0\<rceil>)))) +
                    1 \<longrightarrow>
                  length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [1] = inouts\<^sub>v' x) \<and>
                 (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v x))) 0\<rceil>)))
                     < min (vT_fd_sol_1 (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v n1))) 0\<rceil>))))
                             (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                        (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v (x - Suc 0)))) 0\<rceil>)))) +
                       1 \<longrightarrow>
                  length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [0] = inouts\<^sub>v' x)) \<and>
                (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                 (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v x))) 0\<rceil>)) < 0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [1] = inouts\<^sub>v' x) \<and>
                 (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v x))) 0\<rceil>)) < 0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [0] = inouts\<^sub>v' x)))"
              using hd_tl_2' by presburger
            show "(x = 0 \<longrightarrow>
              (hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v 0))) 0\<rceil>)) < 1 \<longrightarrow>
                length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [1] = inouts\<^sub>v' 0) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v 0))) 0\<rceil>)) < 1 \<longrightarrow>
                length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [0] = inouts\<^sub>v' 0)) \<and>
              (\<not> hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v 0))) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [1] = inouts\<^sub>v' 0) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v 0))) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v 0) = 2 \<and> length(inouts\<^sub>v' 0) = Suc 0 \<and> [0] = inouts\<^sub>v' 0))) \<and>
             (0 < x \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v x))) 0\<rceil>)))
                < min (vT_fd_sol_1 (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v n1))) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v (x - Suc 0)))) 0\<rceil>)))) +
                  1 \<longrightarrow>
                length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [1] = inouts\<^sub>v' x) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v x))) 0\<rceil>)))
                   < min (vT_fd_sol_1 (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v n1))) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v (x - Suc 0)))) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [0] = inouts\<^sub>v' x)) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v x))) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [1] = inouts\<^sub>v' x) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (inouts\<^sub>v x))) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 2 \<and> length(inouts\<^sub>v' x) = Suc 0 \<and> [0] = inouts\<^sub>v' x)))"
            using hd_tl_2' a1'  by blast
          qed
      qed
    then have f8_2: "... = FBlock (\<lambda>x n. True) 2 1 ?f8_f'"
      proof -
        have "\<forall>x na. (1 \<le> (if hd(x na) = 0 then 1::real else 0) * 2) = (hd(x na) = 0)"
          by simp
        then show ?thesis
        proof -
          have "FBlock (\<lambda>f n. True) 2 1 (\<lambda>f n. [if 
              real_of_int (int32 (RoundZero (real_of_int \<lceil>(Rate::real) * max (f n!(Suc 0)) 0\<rceil>))) < 
              (if (1::real) \<le> (if hd (f n) = 0 then 1 else 0) * 2 then (if n = 0 then 0 else 
                min (vT_fd_sol_1 (\<lambda>n. real_of_int (int32 (RoundZero (real_of_int \<lceil>(Rate::real) * 
                    max (f n!(Suc 0)) 0\<rceil>)))) 
            (\<lambda>n. if hd (f n) = 0 then 1 else 0) (n - 1)) (real_of_int (int32 (RoundZero (real_of_int 
              \<lceil>(Rate::real) * max (f (n - 1)!(Suc 0)) 0\<rceil>))))) + 1 else 0) then 1 else 0]) = 
          FBlock (\<lambda>f n. True) 2 1 (\<lambda>f n. [if real_of_int (int32 (RoundZero (real_of_int \<lceil>(Rate::real) 
            * max (f n!(Suc 0)) 0\<rceil>))) < (if hd (f n) = 0 then (if n = 0 then 0 else min (vT_fd_sol_1 
            (\<lambda>n. real_of_int (int32 (RoundZero (real_of_int \<lceil>(Rate::real) * max (f n!(Suc 0)) 0\<rceil>)))) 
            (\<lambda>n. if hd (f n) = 0 then 1 else 0) (n - 1)) (real_of_int (int32 (RoundZero (real_of_int 
            \<lceil>(Rate::real) * max (f (n - 1)!(Suc 0)) 0\<rceil>))))) + 1 else 0) then 1 else 0]) \<or> 
            (\<forall>f n. [if real_of_int (int32 (RoundZero (real_of_int \<lceil>(Rate::real) * max (f n!(Suc 0)) 0\<rceil>))) < 
            (if (1::real) \<le> (if hd (f n) = (0::real) then 1 else 0) * 2 then (if n = 0 then 0 else min 
              (vT_fd_sol_1 (\<lambda>n. real_of_int (int32 (RoundZero (real_of_int \<lceil>(Rate::real) * 
              max (f n!(Suc 0)) 0\<rceil>)))) (\<lambda>n. if hd (f n) = 0 then 1 else 0) (n - 1)) 
              (real_of_int (int32 (RoundZero (real_of_int \<lceil>(Rate::real) * max (f (n - 1)!(Suc 0)) 0\<rceil>))))) + 1 else 0) 
              then 1::real else 0] = [if real_of_int (int32 (RoundZero (real_of_int \<lceil>(Rate::real) * 
              max (f n!(Suc 0)) 0\<rceil>))) < (if hd (f n) = 0 then (if n = 0 then 0 else min (vT_fd_sol_1 
              (\<lambda>n. real_of_int (int32 (RoundZero (real_of_int \<lceil>(Rate::real) * max (f n!(Suc 0)) 0\<rceil>)))) 
              (\<lambda>n. if hd (f n) = 0 then 1 else 0) (n - 1)) (real_of_int (int32 (RoundZero (real_of_int
               \<lceil>(Rate::real) * max (f (n - 1)!(Suc 0)) 0\<rceil>))))) + 1 else 0) then 1 else 0])"
            by auto
          then show ?thesis
            by force
        qed
      qed
    have simblock_f8: "SimBlock 2 1 (FBlock (\<lambda>x n. True) 2 1 ?f8_f')"
      using simblock_f7 SimBlock_variableTimer_simp SimBlock_FBlock_seq_comp f8_0 f8_1 f8_2 by fastforce
    (* (((LopAND 3) \<parallel>\<^sub>B (LopOR 2)) ;; latch) *)
    let ?f9_f = "(\<lambda>x n. [if (x n)!0 = 0 \<or> (x n)!1 = 0 \<or> (x n)!2 = 0 then 0 else 1,
                        if (x n)!3 = 0 \<and> (x n)!4 = 0 then 0 else 1])"
    let ?f9 = "FBlock (\<lambda>x n. True) 5 2 ?f9_f"
    have f9: "((LopAND 3) \<parallel>\<^sub>B (LopOR 2)) = FBlock (\<lambda>x n. True) (3+2) (1+1) 
        (\<lambda>x n. (((f_LopAND \<circ> (\<lambda>xx nn. take 3 (xx nn))) x n) @ 
                ((f_LopOR \<circ> (\<lambda>xx nn. drop 3 (xx nn)))) x n))"
      using SimBlock_LopAND SimBlock_LopOR FBlock_parallel_comp 
      by (simp add: LopAND_def LopOR_def)
    then have f9_0: "... = FBlock (\<lambda>x n. True) (3+2) (1+1) ?f9_f"
      proof -
        show ?thesis
          apply (simp add: FBlock_def f_LopAND_def f_LopOR_def)
          apply (rel_simp)
          apply (rule iffI)
          apply (clarify)
          defer
          apply (clarify)
          defer
          proof -
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::nat
            assume a1: "\<forall>x. (LOr (drop 3 (inouts\<^sub>v x)) \<longrightarrow>
              (LAnd (take 3 (inouts\<^sub>v x)) \<longrightarrow>
               length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [1, 1] = inouts\<^sub>v' x) \<and>
              (\<not> LAnd (take 3 (inouts\<^sub>v x)) \<longrightarrow>
               length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> LOr (drop 3 (inouts\<^sub>v x)) \<longrightarrow>
              (LAnd (take 3 (inouts\<^sub>v x)) \<longrightarrow>
               length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [1, 0] = inouts\<^sub>v' x) \<and>
              (\<not> LAnd (take 3 (inouts\<^sub>v x)) \<longrightarrow>
               length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 0] = inouts\<^sub>v' x))"
            from a1 have len_5: "\<forall>x. length(inouts\<^sub>v x) = 5"
              by blast
            have take_3: "take 3 (inouts\<^sub>v x) = [(inouts\<^sub>v x)!0, (inouts\<^sub>v x)!1, (inouts\<^sub>v x)!2]"
              using len_5 by (smt Cons_nth_drop_Suc Suc_1 Suc_eq_plus1 Suc_mono add_Suc_right 
                  add_diff_cancel_right' drop_0 numeral_3_eq_3 numeral_Bit1 numeral_eq_one_iff 
                    numeral_plus_one take_Suc_Cons take_eq_Nil zero_less_numeral)
            have land_take_3: 
              "LAnd (take 3 (inouts\<^sub>v x)) = (\<not> ((inouts\<^sub>v x)!0 = 0 \<or> (inouts\<^sub>v x)!1 = 0 \<or> (inouts\<^sub>v x)!2 = 0))"
              by (simp add: take_3)
            have drop_3: "drop 3 (inouts\<^sub>v x) = [(inouts\<^sub>v x)!3, (inouts\<^sub>v x)!4]"
              using len_5
              by (metis Cons_nth_drop_Suc add_Suc cancel_ab_semigroup_add_class.add_diff_cancel_left' 
              drop_eq_Nil eval_nat_numeral(2) eval_nat_numeral(3) lessI numeral_Bit0 order_refl pos2 
              semiring_norm(26) semiring_norm(27) zero_less_diff)
            have lor_drop_3: "LOr (drop 3 (inouts\<^sub>v x)) = (\<not>((inouts\<^sub>v x)!3 = 0 \<and> (inouts\<^sub>v x)!4 = 0))"
              by (simp add: drop_3)
            show "(inouts\<^sub>v x!(3) = 0 \<and> inouts\<^sub>v x!(4) = 0 \<longrightarrow>
              (inouts\<^sub>v x!(0) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 0] = inouts\<^sub>v' x) \<and>
              (inouts\<^sub>v x!(Suc 0) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 0] = inouts\<^sub>v' x) \<and>
              (inouts\<^sub>v x!(2) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 0] = inouts\<^sub>v' x) \<and>
              (\<not> inouts\<^sub>v x!(0) = 0 \<and> \<not> inouts\<^sub>v x!(Suc 0) = 0 \<and> \<not> inouts\<^sub>v x!(2) = 0 \<longrightarrow>
               length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [1, 0] = inouts\<^sub>v' x)) \<and>
             ((inouts\<^sub>v x!(3) = 0 \<longrightarrow> \<not> inouts\<^sub>v x!(4) = 0) \<longrightarrow>
              (inouts\<^sub>v x!(0) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 1] = inouts\<^sub>v' x) \<and>
              (inouts\<^sub>v x!(Suc 0) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 1] = inouts\<^sub>v' x) \<and>
              (inouts\<^sub>v x!(2) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 1] = inouts\<^sub>v' x) \<and>
              (\<not> inouts\<^sub>v x!(0) = 0 \<and> \<not> inouts\<^sub>v x!(Suc 0) = 0 \<and> \<not> inouts\<^sub>v x!(2) = 0 \<longrightarrow>
               length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [1, 1] = inouts\<^sub>v' x))"
              using land_take_3 lor_drop_3 a1 len_5 by simp
          next
            fix ok\<^sub>v and inouts\<^sub>v::"nat\<Rightarrow>real list" and ok\<^sub>v' and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::nat
            assume a1: "\<forall>x. (inouts\<^sub>v x!(3) = 0 \<and> inouts\<^sub>v x!(4) = 0 \<longrightarrow>
              (inouts\<^sub>v x!(0) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 0] = inouts\<^sub>v' x) \<and>
              (inouts\<^sub>v x!(Suc 0) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 0] = inouts\<^sub>v' x) \<and>
              (inouts\<^sub>v x!(2) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 0] = inouts\<^sub>v' x) \<and>
              (\<not> inouts\<^sub>v x!(0) = 0 \<and> \<not> inouts\<^sub>v x!(Suc 0) = 0 \<and> \<not> inouts\<^sub>v x!(2) = 0 \<longrightarrow>
               length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [1, 0] = inouts\<^sub>v' x)) \<and>
             ((inouts\<^sub>v x!(3) = 0 \<longrightarrow> \<not> inouts\<^sub>v x!(4) = 0) \<longrightarrow>
              (inouts\<^sub>v x!(0) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 1] = inouts\<^sub>v' x) \<and>
              (inouts\<^sub>v x!(Suc 0) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 1] = inouts\<^sub>v' x) \<and>
              (inouts\<^sub>v x!(2) = 0 \<longrightarrow> length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 1] = inouts\<^sub>v' x) \<and>
              (\<not> inouts\<^sub>v x!(0) = 0 \<and> \<not> inouts\<^sub>v x!(Suc 0) = 0 \<and> \<not> inouts\<^sub>v x!(2) = 0 \<longrightarrow>
               length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [1, 1] = inouts\<^sub>v' x))"
            from a1 have len_5: "\<forall>x. length(inouts\<^sub>v x) = 5"
              by blast
            have take_3: "take 3 (inouts\<^sub>v x) = [(inouts\<^sub>v x)!0, (inouts\<^sub>v x)!1, (inouts\<^sub>v x)!2]"
              using len_5 by (smt Cons_nth_drop_Suc Suc_1 Suc_eq_plus1 Suc_mono add_Suc_right 
                  add_diff_cancel_right' drop_0 numeral_3_eq_3 numeral_Bit1 numeral_eq_one_iff 
                    numeral_plus_one take_Suc_Cons take_eq_Nil zero_less_numeral)
            have land_take_3: 
              "LAnd (take 3 (inouts\<^sub>v x)) = (\<not> ((inouts\<^sub>v x)!0 = 0 \<or> (inouts\<^sub>v x)!1 = 0 \<or> (inouts\<^sub>v x)!2 = 0))"
              by (simp add: take_3)
            have drop_3: "drop 3 (inouts\<^sub>v x) = [(inouts\<^sub>v x)!3, (inouts\<^sub>v x)!4]"
              using len_5
              by (metis Cons_nth_drop_Suc add_Suc cancel_ab_semigroup_add_class.add_diff_cancel_left' 
              drop_eq_Nil eval_nat_numeral(2) eval_nat_numeral(3) lessI numeral_Bit0 order_refl pos2 
              semiring_norm(26) semiring_norm(27) zero_less_diff)
            have lor_drop_3: "LOr (drop 3 (inouts\<^sub>v x)) = (\<not>((inouts\<^sub>v x)!3 = 0 \<and> (inouts\<^sub>v x)!4 = 0))"
              by (simp add: drop_3)
            show "(LOr (drop 3 (inouts\<^sub>v x)) \<longrightarrow>
              (LAnd (take 3 (inouts\<^sub>v x)) \<longrightarrow>
               length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [1, 1] = inouts\<^sub>v' x) \<and>
              (\<not> LAnd (take 3 (inouts\<^sub>v x)) \<longrightarrow>
               length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 1] = inouts\<^sub>v' x)) \<and>
             (\<not> LOr (drop 3 (inouts\<^sub>v x)) \<longrightarrow>
              (LAnd (take 3 (inouts\<^sub>v x)) \<longrightarrow>
               length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [1, 0] = inouts\<^sub>v' x) \<and>
              (\<not> LAnd (take 3 (inouts\<^sub>v x)) \<longrightarrow>
               length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = Suc (Suc 0) \<and> [0, 0] = inouts\<^sub>v' x))"
              using land_take_3 lor_drop_3 a1 len_5 by simp
          qed
      qed
    then have f9_1: "... = ?f9"
      by (metis (no_types, lifting) Suc_eq_plus1 add_Suc nat_1_add_1 numeral_2_eq_2 
          numeral_3_eq_3 numeral_code(3))
    have simblock_f9: "SimBlock 5 2 ?f9"
      using SimBlock_LopAND SimBlock_LopOR SimBlock_FBlock_parallel_comp f9_0 f9_1 f9
      by (smt LopAND_def LopOR_def One_nat_def Suc_eq_plus1 add_Suc numeral_3_eq_3 numeral_Bit1 
          one_add_one zero_less_numeral)
    (* (((LopAND 3) \<parallel>\<^sub>B (LopOR 2)) ;; latch) *)
    let ?f10_f = "(\<lambda>x na. [latch_rec_calc_output 
                    (\<lambda>n1. (if (x n1)!0 = 0 \<or> (x n1)!1 = 0 \<or> (x n1)!2 = 0 then 0 else 1::real)) 
                    (\<lambda>n1. (if (x n1)!3 = 0 \<and> (x n1)!4 = 0 then 0 else 1::real)) 
                    (na)])"
    let ?f10 = "FBlock (\<lambda>x n. True) 5 1 ?f10_f"
    have f10: "(((LopAND 3) \<parallel>\<^sub>B (LopOR 2)) ;; latch) = ?f9 ;; latch_simp_pat'"
      using latch_simp f9 f9_0 f9_1 by simp
    then have f10_0: "... = FBlock (\<lambda>x n. True) 5 1 (latch_simp_pat_f' o ?f9_f)"
      using simblock_f9 FBlock_seq_comp SimBlock_latch_simp' by blast
    then have f10_1: "... = FBlock (\<lambda>x n. True) 5 1 ?f10_f"
      proof -
        have 1: "\<forall>x n. (latch_simp_pat_f' o ?f9_f) x n = ?f10_f x n"
          by (simp)
        then have 2: "(latch_simp_pat_f' o ?f9_f) = ?f10_f"
          using fun_eq by blast
        show ?thesis
          using 2 by (rule FBlock_eq)
      qed
    have simblock_f10: "SimBlock 5 1 ?f10"
      using simblock_f9 SimBlock_latch_simp' SimBlock_FBlock_seq_comp f10_0 f10_1 by fastforce
    (* (
    ( 
      (
         (LopNOT)
         \<parallel>\<^sub>B
         (Id) (* door_open_time: double *)
      ) ;; variableTimer
    )
    \<parallel>\<^sub>B
    (
      (
         (LopAND 3)
         \<parallel>\<^sub>B
         (LopOR 2)
      ) ;; latch
    )
    ) *)
    let ?f11_f = "(\<lambda>x na. [if (if hd(x na) = 0
                   then (if na = 0 then 0
                         else min (vT_fd_sol_1
                                 (\<lambda>n1. (\<lambda>na. real_of_int
                                        (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) n1)
                                 (\<lambda>n1. (if hd(x n1) = 0 then 1::real else 0)) (na - 1))
                            ((\<lambda>na. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>))))
                                  (na - 1))) + 1
                    else 0) > (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) 
          then 1 else 0,
          latch_rec_calc_output 
                    (\<lambda>n1. (if (x n1)!2 = 0 \<or> (x n1)!3 = 0 \<or> (x n1)!4 = 0 then 0 else 1::real)) 
                    (\<lambda>n1. (if (x n1)!5 = 0 \<and> (x n1)!6 = 0 then 0 else 1::real)) 
                    (na)])"
    let ?f11 = "FBlock (\<lambda>x n. True) 7 2 ?f11_f"

    have f11: "((((LopNOT) \<parallel>\<^sub>B (Id) (* door_open_time: double *) ) ;; variableTimer )
                \<parallel>\<^sub>B 
               (((LopAND 3) \<parallel>\<^sub>B(LopOR 2)) ;; latch)) 
        = ?f8 \<parallel>\<^sub>B ?f10"
      using f10 f10_0 f10_1 f8 f8_0 f8_1 by auto
    then have f11_0: "... = FBlock (\<lambda>x n. True) (2+5) (1+1) 
        (\<lambda>x n. (((?f8_f' \<circ> (\<lambda>xx nn. take 2 (xx nn))) x n) @ ((?f10_f \<circ> (\<lambda>xx nn. drop 2 (xx nn)))) x n))"
      using simblock_f8 simblock_f10 FBlock_parallel_comp by blast
    then have f11_1: "... = FBlock (\<lambda>x n. True) (2+5) (1+1) ?f11_f"
      proof -
        show ?thesis
          apply (rule FBlock_eq'')
          defer
          apply auto[1]
          apply auto[1]
          apply (rule allI)+
          apply (clarify)
          proof -
            fix x::"nat \<Rightarrow> real list" and n::nat
            assume a1: "\<forall>n. length(x n) = 2 + 5"
            have hd_take_2: "\<forall>n. hd (take 2 (x n)) = hd (x n)"
              by (simp add: hd_take_m)
            have drop_2_0: "\<forall>n. drop 2 (x n)!0 = (x n)!2"
              using a1 by simp
            have drop_2_1: "\<forall>n. drop 2 (x n)!1 = (x n)!3"
              using a1 by simp
            have drop_2_1': "\<forall>n. drop 2 (x n)!(Suc 0) = (x n)!3"
              using a1 by simp
            have drop_2_2: "\<forall>n. drop 2 (x n)!2 = (x n)!4"
              using a1 by simp
            have drop_2_3: "\<forall>n. drop 2 (x n)!3 = (x n)!5"
              using a1 by simp
            have drop_2_4: "\<forall>n. drop 2 (x n)!4 = (x n)!6"
              using a1 by simp
            let ?lhs1 = "((\<lambda>x na. [if real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))
                        < (if hd (x na) = 0
                           then (if na = 0 then 0
                                 else min (vT_fd_sol_1
                                            (\<lambda>n1. real_of_int
                                                   (int32 (RoundZero (real_of_int \<lceil>Rate * max (x n1!(Suc 0)) 0\<rceil>))))
                                            (\<lambda>n1. if hd (x n1) = 0 then 1 else 0) (na - 1))
                                       (real_of_int
                                         (int32 (RoundZero (real_of_int \<lceil>Rate * max (x (na - 1)!(Suc 0)) 0\<rceil>))))) +
                                1
                           else 0)
                     then 1 else 0]) \<circ> (\<lambda>xx nn. take 2 (xx nn))) x n"
            let ?rhs1 = "(\<lambda>x na. [if real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))
                        < (if hd (x na) = 0
                           then (if na = 0 then 0
                                 else min (vT_fd_sol_1
                                            (\<lambda>n1. real_of_int
                                                   (int32 (RoundZero (real_of_int \<lceil>Rate * max (x n1!(Suc 0)) 0\<rceil>))))
                                            (\<lambda>n1. if hd (x n1) = 0 then 1 else 0) (na - 1))
                                       (real_of_int
                                         (int32 (RoundZero (real_of_int \<lceil>Rate * max (x (na - 1)!(Suc 0)) 0\<rceil>))))) +
                                1
                           else 0)
                     then 1 else 0]) x n"
            let ?lhs2 = "((\<lambda>x na. [latch_rec_calc_output
                             (\<lambda>n1. if x n1!(0) = 0 \<or> x n1!(1) = 0 \<or> x n1!(2) = 0 then 0 else 1::real)
                             (\<lambda>n1. if x n1!(3) = 0 \<and> x n1!(4) = 0 then 0 else 1::real) (na)]) 
                          \<circ> (\<lambda>xx nn. drop 2 (xx nn))) x n "
            let ?rhs2 = "(\<lambda>x n. [latch_rec_calc_output 
                    (\<lambda>n1. if x n1!(2) = 0 \<or> x n1!(3) = 0 \<or> x n1!(4) = 0 then 0 else 1::real)
                    (\<lambda>n1. if x n1!(5) = 0 \<and> x n1!(6) = 0 then 0 else 1::real) (n)]) x n"
            let ?rhs1' = "if real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x n!(Suc 0)) 0\<rceil>)))
                 < (if hd (x n) = 0
                    then (if n = 0 then 0
                          else min (vT_fd_sol_1
                                     (\<lambda>n1. real_of_int
                                            (int32 (RoundZero (real_of_int \<lceil>Rate * max (x n1!(Suc 0)) 0\<rceil>))))
                                     (\<lambda>n1. if hd (x n1) = 0 then 1 else 0) (n - 1))
                                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x (n - 1)!(Suc 0)) 0\<rceil>))))) +
                         1::real
                    else 0)
              then 1::real else 0"
            let ?rhs2' = "latch_rec_calc_output 
                      (\<lambda>n1. if x n1!(2) = 0 \<or> x n1!(3) = 0 \<or> x n1!(4) = 0 then 0 else 1::real)
                      (\<lambda>n1. if x n1!(5) = 0 \<and> x n1!(6) = 0 then 0 else 1::real) (n)"
            from a1 hd_take_2 have f1: "?lhs1 = ?rhs1"
              by (simp)
            have 11: "\<forall>na. (\<lambda>n1. if drop 2 (x n1)!(0) = 0 \<or> drop 2 (x n1)!(Suc 0) = 0 \<or> drop 2 (x n1)!(2) = 0 then 0 else 1) na
                = (\<lambda>n1. if x n1!(2) = 0 \<or> x n1!(3) = 0 \<or> x n1!(4) = 0 then 0 else 1) na"
              using drop_2_0 drop_2_1' drop_2_2 drop_2_3 drop_2_4 a1 by simp
            then have 12: "(\<lambda>n1. if drop 2 (x n1)!(0) = 0 \<or> drop 2 (x n1)!(Suc 0) = 0 \<or> drop 2 (x n1)!(2) = 0 then 0 else 1)
                = (\<lambda>n1. if x n1!(2) = 0 \<or> x n1!(3) = 0 \<or> x n1!(4) = 0 then 0 else 1)"
              by (rule fun_eq)
            have 21: "\<forall>na. (\<lambda>n1. if drop 2 (x n1)!(3) = 0 \<and> drop 2 (x n1)!(4) = 0 then 0 else 1) na
              = (\<lambda>n1. if x n1!(5) = 0 \<and> x n1!(6) = 0 then 0 else 1) na"
              using drop_2_0 drop_2_1' drop_2_2 drop_2_3 drop_2_4 a1 by simp
            then have 22: "(\<lambda>n1. if drop 2 (x n1)!(3) = 0 \<and> drop 2 (x n1)!(4) = 0 then 0 else 1)
              = (\<lambda>n1. if x n1!(5) = 0 \<and> x n1!(6) = 0 then 0 else 1)"
              by (rule fun_eq)
            have latch_eq: 
                  "latch_rec_calc_output (\<lambda>n1. if drop 2 (x n1)!(0) = 0 \<or> drop 2 (x n1)!(Suc 0) = 0 
                    \<or> drop 2 (x n1)!(2) = 0 then 0 else 1)
                    (\<lambda>n1. if drop 2 (x n1)!(3) = 0 \<and> drop 2 (x n1)!(4) = 0 then 0 else 1) (n - Suc 0) 
               =  latch_rec_calc_output (\<lambda>n1. if x n1!(2) = 0 \<or> x n1!(3) = 0 \<or> x n1!(4) = 0 then 0 else 1)
                    (\<lambda>n1. if x n1!(5) = 0 \<and> x n1!(6) = 0 then 0 else 1) (n - Suc 0)"
              by (simp add: 12 22)
            have f2: "?lhs2 = ?rhs2"
              apply (simp)
              using latch_eq drop_2_0 drop_2_1 drop_2_2 drop_2_3 drop_2_4 a1 
              using numeral_1_eq_Suc_0 numerals(1) by presburger 
            have f12: "(?lhs1 @ ?lhs2) = ?rhs1 @ ?rhs2"
              using f1 f2 by simp
            then have f21: "... = [?rhs1', ?rhs2']"
              by simp
            show "(?lhs1 @ ?lhs2) = [?rhs1', ?rhs2']"
              using f12 f21 by (simp)
          qed
      qed
    then have f11_2: "... = ?f11"
      by (smt Suc_eq_plus1 add_Suc_right numeral_Bit1 numeral_One one_add_one)
    have simblock_f11: "SimBlock 7 2 ?f11"
      using simblock_f8 simblock_f10 SimBlock_FBlock_parallel_comp
      by (smt Suc_numeral add.commute add_Suc_right add_numeral_left f11_0 f11_1 numeral_Bit1 
          numeral_One one_add_one)
    (* (
        (
          (
            (
              Split2 (* door_closed (boolean, 1/10s) is split into two *) 
              \<parallel>\<^sub>B
              Id (* door_open_time: double *)
            ) ;; Router 3 [0,2,1]
          )
          \<parallel>\<^sub>B 
          post_mode
        )
        \<parallel>\<^sub>B
        (
           (UnitDelay 1.0 ;; LopNOT)
           \<parallel>\<^sub>B
           (UnitDelay 0) (* Delay2 *)
        )
      ) ;;
      (
        ( 
          (
             (LopNOT)
             \<parallel>\<^sub>B
             (Id) (* door_open_time: double *)
          ) ;; variableTimer
        )
        \<parallel>\<^sub>B
        (
          (
             (LopAND 3)
             \<parallel>\<^sub>B
             (LopOR 2)
          ) ;; latch
        )
      ) *)
    let ?f12_f_1 = "\<lambda>x na. if (if hd(x na) = 0
                   then (if na = 0 then 0
                         else min (vT_fd_sol_1
                                 (\<lambda>n1. (\<lambda>na. real_of_int
                                        (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) n1)
                                 (\<lambda>n1. (if hd(x n1) = 0 then 1::real else 0)) (na - 1))
                            ((\<lambda>na. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>))))
                                  (na - 1))) + 1::real
                    else 0) > (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x na!(Suc 0)) 0\<rceil>)))) 
          then 1::real else 0"
    let ?f12_f_2 = "\<lambda>x na. latch_rec_calc_output 
                    (\<lambda>n1. (if hd(x n1) = 0 \<or> (if (n1 > 0 \<and> (x (n1-1))!2 = 4) then 1::real else 0) = 0 
                    \<or> (if (x n1)!2 = 8 then 1::real else 0) = 0 then 0 else 1::real)) 
                    (\<lambda>n1. (if ((if n1 = 0 then 0 else (if (x (n1 - 1))!3 = 0 then 1::real else 0))) = 0 \<and> 
                            (if n1 = 0 then 0 else (x (n1 - 1))!4) = 0 then 0 else 1::real)) 
                    (na)"
    let ?f12_f_2' = "\<lambda>x na. (latch_rec_calc_output 
                      (\<lambda>n1. (if hd(x n1) = 0 \<or> n1 = 0 \<or> (x (n1-1))!2 \<noteq> 4 \<or> (x n1)!2 \<noteq> 8
                          then 0 else 1::real)) 
                      (\<lambda>n1. (if ((n1 = 0) \<or> ((x (n1 - 1))!3 \<noteq> 0 \<and> (x (n1 - 1))!4 = 0))
                          then 0 else 1::real))
                      (na))"
    let ?f12_f = "(\<lambda>x na. [?f12_f_1 x na, ?f12_f_2 x na])"
    let ?f12 = "FBlock (\<lambda>x n. True) 5 2 ?f12_f"
    let ?f12_f' = "(\<lambda>x na. [?f12_f_1 x na, ?f12_f_2' x na])"
    let ?f12' = "FBlock (\<lambda>x n. True) 5 2 ?f12_f'"
    have f12_f_2_eq: "\<forall>x n. ?f12_f_2 x n = ?f12_f_2' x n"
      apply (rule allI)+
      apply (simp)
      apply (induct_tac n)
      apply auto[1]
      by simp
    have f12: "(
        (
          (
            (
              Split2 (* door_closed (boolean, 1/10s) is split into two *) 
              \<parallel>\<^sub>B
              Id (* door_open_time: double *)
            ) ;; Router 3 [0,2,1]
          )
          \<parallel>\<^sub>B 
          post_mode
        )
        \<parallel>\<^sub>B
        (
           (UnitDelay 1.0 ;; LopNOT)
           \<parallel>\<^sub>B
           (UnitDelay 0) (* Delay2 *)
        )
      ) ;;
      (
        ( 
          (
             (LopNOT)
             \<parallel>\<^sub>B
             (Id) (* door_open_time: double *)
          ) ;; variableTimer
        )
        \<parallel>\<^sub>B
        (
          (
             (LopAND 3)
             \<parallel>\<^sub>B
             (LopOR 2)
          ) ;; latch
        )
      ) = ?f6 ;; ?f11"
      using f11 f11_0 f11_1 f11_2 f8 f8_0 f8_1 f6 f6_0 f6_1 f6_2 by auto
    then have f12_0: "... = FBlock (\<lambda>x n. True) 5 2 (?f11_f o ?f6_f)"
      using simblock_f6 simblock_f11 FBlock_seq_comp by blast
    then have f12_1: "... = FBlock (\<lambda>x n. True) 5 2 (?f12_f)"
      proof -
        have hd_tl_eq: "\<forall>x n. length(x n) > 1 \<longrightarrow> hd (tl (x n)) = (x n)!(Suc 0)"
          by (metis One_nat_def drop_0 drop_Suc hd_drop_conv_nth)
        show ?thesis
          apply (rule FBlock_eq'')
          defer
          apply auto[1]
          apply auto[1]
          apply (simp)
          apply (rule allI)+
          apply (clarify)
          apply (rule conjI)
          apply (simp add: hd_tl_eq)
          apply (clarify, rule conjI)
          defer
          apply (simp add: hd_tl_eq)
          proof -
            fix x::"nat \<Rightarrow> real list" and n::nat
            assume a1: "\<forall>na. length(x na) = 5"
            have vT_eq: "(vT_fd_sol_1 (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (x n1))) 0\<rceil>))))
                      (\<lambda>n1. if hd (x n1) = 0 then 1 else 0) (n - Suc 0))
              = (vT_fd_sol_1 (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x n1!(Suc 0)) 0\<rceil>))))
                      (\<lambda>n1. if hd (x n1) = 0 then 1 else 0) (n - Suc 0))"
              by (simp add: hd_tl_eq a1)
            have real_eq: "real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (x n))) 0\<rceil>)))
              = real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x n!(Suc 0)) 0\<rceil>)))"
              by (simp add: hd_tl_eq a1)
            show a2: "hd (x n) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (x n))) 0\<rceil>)))
                < min (vT_fd_sol_1 (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (x n1))) 0\<rceil>))))
                        (\<lambda>n1. if hd (x n1) = 0 then 1 else 0) (n - Suc 0))
                   (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (x (n - Suc 0)))) 0\<rceil>)))) +
                  1 \<longrightarrow>
                real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x n!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1 (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (x n1) = 0 then 1 else 0) (n - Suc 0))
                   (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x (n - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (x n))) 0\<rceil>)))
                   < min (vT_fd_sol_1 (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (x n1))) 0\<rceil>))))
                           (\<lambda>n1. if hd (x n1) = 0 then 1 else 0) (n - Suc 0))
                      (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (hd (tl (x (n - Suc 0)))) 0\<rceil>)))) +
                     1 \<longrightarrow>
                \<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x n!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1 (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (x n1) = 0 then 1 else 0) (n - Suc 0))
                      (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (x (n - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1) "
                using vT_eq real_eq a1 hd_tl_eq
                by (simp add: hd_tl_eq)
          qed
      qed 
    then have f12_2: "... = FBlock (\<lambda>x n. True) 5 2 (?f12_f')"
      proof -
        show ?thesis
          apply (rule FBlock_eq'')
          using f12_f_2_eq apply blast
          apply simp
          by simp
      qed
    have simblock_f12: "SimBlock 5 2 ?f12'"
      using simblock_f6 simblock_f11 FBlock_seq_comp SimBlock_FBlock_seq_comp f12_0 f12_1 f12_2
      by smt
    (* LopAND 2;; rise1Shot ;; Split2 *)
    let ?f13_f = "(\<lambda>x n. [if ((hd(x n) \<noteq> 0 \<and> hd(tl(x n)) \<noteq> 0) \<and> 
                    (n > 0 \<and> (hd(x (n-1)) = 0 \<or> hd(tl(x (n-1))) = 0))) then 1 else 0])"
    let ?f13 = "FBlock (\<lambda>x n. True) 2 1 ?f13_f"
    have f13: "LopAND 2;; rise1Shot = LopAND 2 ;; rise1Shot_simp_pat"
      by (simp add: rise1Shot_simp)
    then have f13_0: "... = FBlock (\<lambda>x n. True) 2 1 (rise1Shot_simp_pat_f o f_LopAND)"
      using SimBlock_rise1Shot_simp SimBlock_LopAND FBlock_seq_comp 
      by (simp add: LopAND_def)
    then have f13_1: "... =  ?f13"
      proof -
        show ?thesis
          apply (rule FBlock_eq'')
          defer
          apply (simp add: f_LopAND_def)
          apply (simp add: f_LopAND_def)
          apply (rule allI)+
          apply (clarify)
          apply (simp add: f_LopAND_def)
          apply (clarify)
          proof -
            fix x:: "nat \<Rightarrow> real list" and n::nat
            assume a1: "\<forall>n. length(x n) = 2"
            assume a2: "n > 0"
            from a1 a2 have land_1: "LAnd (x (n - Suc 0)) = 
                    (\<not> hd (x (n - Suc 0)) = 0 \<and> \<not> hd (tl (x (n - Suc 0))) = 0)"
              using LAnd.simps(1) LAnd.simps(2) append_eq_Cons_conv hd_Cons_tl length_Cons list.sel(3) 
                    list_equal_size2 tl_append2 by smt
            from a1 a2 have land_2: "LAnd (x n) = 
                    (\<not> hd (x n) = 0 \<and> \<not> hd (tl (x n)) = 0)"
              using LAnd.simps(1) LAnd.simps(2) append_eq_Cons_conv hd_Cons_tl length_Cons list.sel(3) 
                    list_equal_size2 tl_append2 by smt
            show "(LAnd (x (n - Suc 0)) \<longrightarrow>
              hd (x n) = 0 \<or> hd (tl (x n)) = 0 \<or> \<not> hd (x (n - Suc 0)) = 0 \<and> \<not> hd (tl (x (n - Suc 0))) = 0) \<and>
             (\<not> LAnd (x (n - Suc 0)) \<longrightarrow>
              (LAnd (x n) \<longrightarrow>
               \<not> hd (x n) = 0 \<and> \<not> hd (tl (x n)) = 0 \<and> (hd (x (n - Suc 0)) = 0 \<or> hd (tl (x (n - Suc 0))) = 0)) \<and>
              (\<not> LAnd (x n) \<longrightarrow>
               hd (x n) = 0 \<or> hd (tl (x n)) = 0 \<or> \<not> hd (x (n - Suc 0)) = 0 \<and> \<not> hd (tl (x (n - Suc 0))) = 0))"
              using land_1 land_2 by blast
          qed
      qed
    have simblock_f13: "SimBlock 2 1 ?f13"
      using SimBlock_rise1Shot_simp SimBlock_LopAND SimBlock_FBlock_seq_comp
      by (metis (no_types, lifting) LopAND_def f13_0 f13_1 pos2)
    (* LopAND 2;; rise1Shot ;; Split2 *)
    let ?f14_f = "(\<lambda>x n. [if ((hd(x n) \<noteq> 0 \<and> hd(tl(x n)) \<noteq> 0) \<and> 
                    (n > 0 \<and> (hd(x (n-1)) = 0 \<or> hd(tl(x (n-1))) = 0))) then 1 else 0,
                          if ((hd(x n) \<noteq> 0 \<and> hd(tl(x n)) \<noteq> 0) \<and> 
                    (n > 0 \<and> (hd(x (n-1)) = 0 \<or> hd(tl(x (n-1))) = 0))) then 1 else 0])"
    let ?f14 = "FBlock (\<lambda>x n. True) 2 2 ?f14_f"
    have f14: "LopAND 2;; rise1Shot ;; Split2 = ?f13 ;; Split2"
      by (metis RA1 f13_0 f13_1 rise1Shot_simp)
    then have f14_0: "... = FBlock (\<lambda>x n. True) 2 2 (f_Split2 o ?f13_f)"
      using simblock_f13 SimBlock_Split2  FBlock_seq_comp 
      by (simp add: Split2_def)
    then have f14_1: "... = ?f14"
      proof -
        show ?thesis
          apply (rule FBlock_eq)
          using f_Split2_def
          by fastforce
      qed
    have simblock_f14: "SimBlock 2 2 ?f14"
      using simblock_f13 SimBlock_Split2 SimBlock_FBlock_seq_comp
      by (metis (no_types, lifting) Split2_def f14_0 f14_1)
    (* *)
    let ?f15_f = "(\<lambda>x n. [if (((?f12_f_1 x n) \<noteq> 0 \<and> (?f12_f_2' x n) \<noteq> 0) \<and> 
                    (n > 0 \<and> ((?f12_f_1 x (n-1)) = 0 \<or> (?f12_f_2' x (n-1)) = 0))) then 1 else 0,
                          if (((?f12_f_1 x n) \<noteq> 0 \<and> (?f12_f_2' x n) \<noteq> 0) \<and> 
                    (n > 0 \<and> ((?f12_f_1 x (n-1)) = 0 \<or> (?f12_f_2' x (n-1)) = 0))) then 1 else 0])"
    let ?f15 = "FBlock (\<lambda>x n. True) 5 2 ?f15_f"
    have f15: "(
        (
          (
            (
              (
                Split2 (* door_closed (boolean, 1/10s) is split into two *) 
                \<parallel>\<^sub>B
                Id (* door_open_time: double *)
              ) ;; Router 3 [0,2,1]
            )
            \<parallel>\<^sub>B 
            post_mode
          )
          \<parallel>\<^sub>B
          (
             (UnitDelay 1.0 ;; LopNOT)
             \<parallel>\<^sub>B
             (UnitDelay 0) (* Delay2 *)
          )
        ) ;;
        (
          ( 
            (
               (LopNOT)
               \<parallel>\<^sub>B
               (Id) (* door_open_time: double *)
            ) ;; variableTimer
          )
          \<parallel>\<^sub>B
          (
            (
               (LopAND 3)
               \<parallel>\<^sub>B
               (LopOR 2)
            ) ;; latch
          )
        ) ;; LopAND 2;; rise1Shot ;; Split2) = ?f12' ;; ?f14"
      by (smt RA1 f12 f12_0 f12_1 f12_2 f14 f14_0 f14_1)
    then have f15_0: "... = FBlock (\<lambda>x n. True) 5 2 (?f14_f o ?f12_f')"
      using simblock_f14 simblock_f12 FBlock_seq_comp by blast
    then have f15_1: "... = ?f15"
      proof -
        have 1: "\<forall>x n. ((?f14_f o ?f12_f') x n = ?f15_f x n)"
          apply (rule allI)+
          by (simp)
        have 2: "(?f14_f o ?f12_f') = ?f15_f"
          using 1 fun_eq by blast
        show ?thesis
          apply (rule FBlock_eq)
          using 1 2 by blast
      qed
    have simblock_f15: "SimBlock 5 2 ?f15"
      using simblock_f14 simblock_f12 SimBlock_FBlock_seq_comp f15_0 f15_1
      by (metis (no_types, lifting))
    have inps_f15: "inps ?f15 = 5"
      using simblock_f15 inps_P by blast
    have outps_f15: "outps ?f15 = 2"
      using simblock_f15 outps_P by blast
    (* *)
    have f16: "post_landing_finalize_1 = ?f15 f\<^sub>D (4, 1)"
      using f15 f15_0 f15_1 post_landing_finalize_1_def by presburger
    show ?thesis
      apply (simp only: plf_rise1shot_simp_def)
      using f16 simblock_f15 by presburger
  qed

text {* Finally, @{text "post_landing_finalize_1"} is simplified to a design with a feedback. *}
lemma post_landing_finalize_1_simp:
  "post_landing_finalize_1 = plf_rise1shot_simp f\<^sub>D (4, 1)"
  using post_landing_finalize_1_simp_simblock by blast

lemma post_landing_finalize_1_simblock:
  "SimBlock 5 2 plf_rise1shot_simp"
  using post_landing_finalize_1_simp_simblock by blast

lemma inps_plf_rise1shot:
  "inps plf_rise1shot_simp = 5"
  using post_landing_finalize_1_simblock inps_P by blast

lemma outps_plf_rise1shot:
  "outps plf_rise1shot_simp = 2"
  using post_landing_finalize_1_simblock outps_P by blast
  
subsection {* Verification \label{sec:post_landing_veri}*}

(* post_landing_finalize_1 has four inputs and one output
  input 1: door_closed, boolean
  input 2: door_open_time, double 
  input 3: mode: in1, uint32, 1/10s
  input 4: ac_on_ground, boolean
  
  output: final_event, boolean
*)

(*
  A successful landing:
  - LANDING: ac_on_ground = true, door_closed = true, mode = LANDING, door_open_time fixed
    + latch = previous latch (S = 0 and R = 0 (finalize_event = 0))
  - GROUND: ac_on_ground = true, door_closed = true, mode = GROUND, door_open_time fixed
    + latch = 1 (S = 1 and R = 0)
    + count = 0 (door_closed = true)
  - Door is open: ac_on_ground = true, door_closed = false, mode = GROUND, door_open_time fixed
    + latch = 1 (previous latch as S = 0 (door_closed = false) and R = 0 (finalize_event = 0))
    + count = 1 (door_closed = false)
  - Door is open: ac_on_ground = true, door_closed = false, mode = GROUND, door_open_time fixed
    + latch = 1 (previous latch as S = 0 (door_closed = false) and R = 0 (finalize_event = 0))
    + count = 2 (door_closed = false)
  - ...
  - Door is open: ac_on_ground = true, door_closed = false, mode = GROUND, door_open_time fixed
    + latch = 1 (previous latch as S = 0 (door_closed = false) and R = 0 (finalize_event = 0))
    + count = door_open_time + 1 (door_closed = false)
    + finalize_event = 1
  - Door is open: ac_on_ground = true, door_closed = false, mode = GROUND, door_open_time fixed
    + latch = 0 (S = 0 (door_closed = false) and R = 1 (previous finalize_event = 1))
    + count = door_open_time + 1 (door_closed = false and min)
    + finalize_event = 0
  - Door is open: ac_on_ground = true, door_closed = false, mode = GROUND, door_open_time fixed
    + latch = 0 (previous latch as S = 0 (door_closed = false) and R = 0 (previous finalize_event = 0))
    + count = door_open_time + 1 (door_closed = false and min)
    + finalize_event = 0
*)
text {* Here we assume the maximum door open time is 1000s. It could be a value less than 214748364. *}
abbreviation "max_door_open_time \<equiv> 1000"

subsubsection {* Requirement 01 \label{ssec:plf_req1} *}
text {* @{text "post_landing_finalize_req_01"}: A finalize event will be broadcast after the 
aircraft door has been open continuously for @{text "door_open_time"} seconds while the aircraft
is on the ground after a successful landing. *}

text {* Here we assume the constant door open time is 20s. It should be a variable but according to 
Assumption 3, it does not change while the aircraft is on the ground. So we can regard it as a constant 
after landing. *}
abbreviation "c_door_open_time \<equiv> 20"

text {* @{text "req_01_contract"} is the requirement to be verified. 
Its precondition specifies that @{text "door_closed"} and @{text "ac_on_ground"} are boolean 
and @{text "door_open_time"} is constant. 
Its postcondition specifies that 
\begin{itemize}
  \item it always has four inputs and one output;
  \item the requirement: 
     \begin{itemize}
        \item after a successful landing: door is closed, aircraft is on ground, mode is switched 
            from LANDING (at step $m$) to GROUND (at step $m+1$);
        \item then the door has been open continuously for @{text "door_open_time"} (200): 
            from step $m+2+p$ to $m+2+p+door\_open\_time$ ($m+2+p+200$), therefore the door is closed
            at the step before $p$;
        \item while the aircraft is on ground: @{text "ac_on_ground"} is true and @{text "mode=GROUND"};
        \item additionally, between step $m$ and $p$, the @{text "finalize_event"} is not enabled;
        \item then a @{text "finalize_event"} will be broadcast at step $p+door\_open\_time$
     \end{itemize}
\end{itemize}
*}
definition "req_01_contract \<equiv> ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. 
        (
          (hd(x n) = 0 \<or> hd(x n) = 1) \<and> (* door_closed is boolean *)
          ((x n)!1 = c_door_open_time) \<and> (* door_open_time *)
          ((x n)!3 = 0 \<or> (x n)!3 = 1) (* ac_on_ground is boolean *)
        ))\<guillemotright> (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred)
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>4\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>1\<guillemotright>)) \<and>
      (* m    : LANDING
         m+1  : GROUND 
         ...  : \<not>finalize_event during this time, door may be open for a while but not longer like
                door_open_time
         p-1  : door closed
         p[0] : door open
         ...  : door continuously open
         p[n] : door open for door_open_time seconds, finalize_event enabled.
      *)
      (\<^bold>\<forall> m::nat \<bullet>
        (
         ( (* A successful landing *)
            ( (\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m\<guillemotright>)\<^sub>a)\<^sub>a (3)\<^sub>a =\<^sub>u 1) (* ac_on_ground = true*)
             \<and>(\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m\<guillemotright>)\<^sub>a)\<^sub>a (2)\<^sub>a =\<^sub>u 4) (* mode = LANDING *)
             \<and>(\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m\<guillemotright>)\<^sub>a)\<^sub>a (0)\<^sub>a =\<^sub>u 1) (* door_closed = true *)
            ) \<and>
            ( (\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+1\<guillemotright>)\<^sub>a)\<^sub>a (3)\<^sub>a =\<^sub>u 1) (* ac_on_ground = true*)
             \<and>(\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+1\<guillemotright>)\<^sub>a)\<^sub>a (2)\<^sub>a =\<^sub>u 8) (* mode = GROUND *)
             \<and>(\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+1\<guillemotright>)\<^sub>a)\<^sub>a (0)\<^sub>a =\<^sub>u 1) (* door_closed = true *)
            )
         )  \<Rightarrow>
         ( (* The door is open continuously for door_open_time seconds from (m+p) *)
            \<^bold>\<forall> p::nat \<bullet> 
              (
                ((\<^bold>\<forall> q::nat \<bullet> 
                  ( ((\<guillemotleft>q\<guillemotright> \<le>\<^sub>u \<guillemotleft>c_door_open_time*Rate\<guillemotright>)) \<Rightarrow> 
                      (\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+2+p+q\<guillemotright>)\<^sub>a)\<^sub>a (0)\<^sub>a =\<^sub>u 0) (* door_closed = false *)
                  ) (* The door is continuously open *)
                ) \<and>
                (\<^bold>\<forall> q::nat \<bullet> ((\<guillemotleft>q\<guillemotright> \<le>\<^sub>u \<guillemotleft>p + c_door_open_time*Rate\<guillemotright>) \<Rightarrow> 
                      ((\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+2+q\<guillemotright>)\<^sub>a)\<^sub>a (3)\<^sub>a =\<^sub>u 1) (* ac_on_ground = true *) \<and>
                       (\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+2+q\<guillemotright>)\<^sub>a)\<^sub>a (2)\<^sub>a =\<^sub>u 8) (* mode = GROUND *)))
                ) (* the aircraft is always on the ground from m+2 to m+p+times *) \<and>
                ((\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+2+p-1\<guillemotright>)\<^sub>a)\<^sub>a (0)\<^sub>a =\<^sub>u 1)) (* door_closed = true before $p$ *) \<and>
                (\<^bold>\<forall> q::nat \<bullet> (\<guillemotleft>q\<guillemotright> <\<^sub>u \<guillemotleft>p\<guillemotright>) \<Rightarrow> (head\<^sub>u(($inouts\<acute> (\<guillemotleft>m+2+q\<guillemotright>)\<^sub>a)) =\<^sub>u 0))) 
                  (* finalize_event has not been enabled before p *)
                \<Rightarrow> ($inouts\<acute> (\<guillemotleft>m + 2 + p + c_door_open_time*Rate\<guillemotright>)\<^sub>a) =\<^sub>u \<langle>1\<rangle>
                  (* then the finalize_event is true. *)
              )
         )
      ))))"

text {* @{text "req_01_1_contract"} is the contract for @{text "post_landing_finalize_1"} 
  without feedback: @{text "plf_rise1shot_simp"}. It is similar to @{text "req_01_contract"} except
that 1) it has five inputs and two outputs (the feedback operator will remove one input and one 
output); 2) the 2nd output is equal to the 4th input since they are connected together by 
the feedback loop.
*}
definition "req_01_1_contract \<equiv> ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. 
        (
          (hd(x n) = 0 \<or> hd(x n) = 1) \<and> (* door_closed is boolean *)
          ((x n)!1 = c_door_open_time) \<and> (* door_open_time *)
          ((x n)!3 = 0 \<or> (x n)!3 = 1) (* ac_on_ground is boolean *)
        ))\<guillemotright> (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred)
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>5\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>2\<guillemotright>)) \<and>
      (* m    : LANDING
         m+1  : GROUND 
         ...  : \<not>finalize_event during this time, door may be open for a while but not longer like
                door_open_time
         p-1  : door closed
         p[0] : door open
         ...  : door continuously open
         p[n] : door open for door_open_time seconds, finalize_event enabled.
      *)
      (\<^bold>\<forall> m::nat \<bullet>
        (
         ( (* A successful landing *)
            ( (\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m\<guillemotright>)\<^sub>a)\<^sub>a (3)\<^sub>a =\<^sub>u 1) (* ac_on_ground = true*)
             \<and>(\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m\<guillemotright>)\<^sub>a)\<^sub>a (2)\<^sub>a =\<^sub>u 4) (* mode = LANDING *)
             \<and>(\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m\<guillemotright>)\<^sub>a)\<^sub>a (0)\<^sub>a =\<^sub>u 1) (* door_closed = true *)
            ) \<and>
            ( (\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+1\<guillemotright>)\<^sub>a)\<^sub>a (3)\<^sub>a =\<^sub>u 1) (* ac_on_ground = true*)
             \<and>(\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+1\<guillemotright>)\<^sub>a)\<^sub>a (2)\<^sub>a =\<^sub>u 8) (* mode = GROUND *)
             \<and>(\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+1\<guillemotright>)\<^sub>a)\<^sub>a (0)\<^sub>a =\<^sub>u 1) (* door_closed = true *)
            ) \<and>
            (\<^bold>\<forall> n::nat \<bullet> (head\<^sub>u(tail\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a (4)\<^sub>a))
            (* 4th input is equal to output*)
         )  \<Rightarrow>
         ( (* The door is open continuously for door_open_time seconds from (m+p) *)
            \<^bold>\<forall> p::nat \<bullet> 
              (
                ((\<^bold>\<forall> q::nat \<bullet> 
                  ( ((\<guillemotleft>q\<guillemotright> \<le>\<^sub>u \<guillemotleft>c_door_open_time*Rate\<guillemotright>)) \<Rightarrow> 
                      (\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+2+p+q\<guillemotright>)\<^sub>a)\<^sub>a (0)\<^sub>a =\<^sub>u 0) (* door_closed = false *)
                  ) (* The door is continuously open *)
                ) \<and>
                (\<^bold>\<forall> q::nat \<bullet> ((\<guillemotleft>q\<guillemotright> \<le>\<^sub>u \<guillemotleft>p + c_door_open_time*Rate\<guillemotright>) \<Rightarrow> 
                      ((\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+2+q\<guillemotright>)\<^sub>a)\<^sub>a (3)\<^sub>a =\<^sub>u 1) (* ac_on_ground = true *) \<and>
                       (\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+2+q\<guillemotright>)\<^sub>a)\<^sub>a (2)\<^sub>a =\<^sub>u 8) (* mode = GROUND *)))
                ) (* the aircraft is always on the ground from m+2 to m+p+times *) \<and>
                ((\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+2+p-1\<guillemotright>)\<^sub>a)\<^sub>a (0)\<^sub>a =\<^sub>u 1)) (* door_closed = true *) \<and>
                (\<^bold>\<forall> q::nat \<bullet> (\<guillemotleft>q\<guillemotright> <\<^sub>u \<guillemotleft>p\<guillemotright>) \<Rightarrow> (head\<^sub>u(($inouts\<acute> (\<guillemotleft>m+2+q\<guillemotright>)\<^sub>a)) =\<^sub>u 0))) 
                  (* finalize_event has not been enabled before p *)
                \<Rightarrow> ($inouts\<acute> (\<guillemotleft>m + 2 + p + c_door_open_time*Rate\<guillemotright>)\<^sub>a) =\<^sub>u \<langle>1,1\<rangle>
                  (* then the finalize_event is true. *)
              )
         )))))"

lemma SimBlock_req_01_1_contract:
  "SimBlock 5 2 req_01_1_contract"
  apply (simp add: SimBlock_def req_01_1_contract_def)
  apply (rel_auto)
  apply (rule_tac x = "\<lambda>na. [1, 20, if na = 1 then 8 else 4, 1, 0]" in exI)
  apply (rule conjI, simp)
  apply (rule_tac x = "\<lambda>na. [1, 1]" in exI)
  by (simp)
  
lemma inps_req_01_1_contract:
  "inps req_01_1_contract = 5"
  using SimBlock_req_01_1_contract inps_P by blast

lemma outps_req_01_1_contract:
  "outps req_01_1_contract = 2"
  using SimBlock_req_01_1_contract outps_P by blast

text {* In order to verify this requirement, firstly to verify the contract 
 @{text "req_01_1_contract"} refined by @{text "plf_rise1shot_simp"}. *}  
lemma req_01_ref_plf_rise1shot: "req_01_1_contract \<sqsubseteq> plf_rise1shot_simp"
  apply (simp add: FBlock_def plf_rise1shot_simp_def req_01_1_contract_def)
  apply (rule ndesign_refine_intro)
  apply simp
  apply (unfold upred_defs urel_defs)
  apply (simp add: fun_eq_iff relcomp_unfold OO_def
    lens_defs upred_defs alpha_splits Product_Type.split_beta)?
  apply (transfer)
  apply (simp; safe)
  proof -
    fix inouts\<^sub>v inouts\<^sub>v'::"nat \<Rightarrow> real list" and x::nat and xa::nat
    assume a1: "\<forall>x. (hd (inouts\<^sub>v x) = 0 \<or> hd (inouts\<^sub>v x) = 1) \<and>
           inouts\<^sub>v x!(Suc 0) = c_door_open_time \<and> (inouts\<^sub>v x!3 = 0 \<or> inouts\<^sub>v x!3 = 1)"
    let ?P = "\<lambda>x. (x \<le> Suc 0 \<longrightarrow>
            (hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
              (x = 0 \<longrightarrow> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 1 (real_of_int
                           (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                   1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 1 (real_of_int
                              (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                      1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 2 \<and>
               [0, 0] = inouts\<^sub>v' 0 \<and> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 1 (real_of_int
                           (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                   1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 1 (real_of_int
                              (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                      1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)))))) \<and>
            (\<not> hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (x = 0 \<longrightarrow> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 0 (real_of_int
                           (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                   1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 0 (real_of_int
                              (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                      1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 2 \<and>
               [0, 0] = inouts\<^sub>v' 0 \<and> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 0 (real_of_int
                           (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                   1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 0 (real_of_int
                              (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                      1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))))) \<and>
           (\<not> x \<le> Suc 0 \<longrightarrow>
            (hd (inouts\<^sub>v (x - Suc 0)) = 0 \<longrightarrow>
             (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))
              < min (vT_fd_sol_1
                      (\<lambda>n1. real_of_int
                             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                      (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc (Suc 0)))
                 (real_of_int
                   (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc (Suc 0))!(Suc 0)) 0\<rceil>)))) +
                1 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int
                               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int
                     (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int
                                  (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int
                        (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)))) \<and>
             (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))
                 < min (vT_fd_sol_1
                         (\<lambda>n1. real_of_int
                                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                         (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc (Suc 0)))
                    (real_of_int
                      (int32 (RoundZero
                               (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc (Suc 0))!(Suc 0)) 0\<rceil>)))) +
                   1 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int
                               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int
                     (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int
                                  (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int
                        (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))) \<and>
            (\<not> hd (inouts\<^sub>v (x - Suc 0)) = 0 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int
                               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int
                     (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int
                                  (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int
                        (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)))) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int
                               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int
                     (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int
                                  (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int
                        (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))))"
    assume a2: "\<forall>x. ?P x"
(*
x > 1
  door_open(x-1)
    count(x-2)+1 > 200
      door_open(x)
        count(x-1)+1 > 200
          latch x = 1 \<and> latch (x-1) = 0 \<longrightarrow> [1, 1] = inouts\<^sub>v' x
          latch x = 0 \<longrightarrow> [0, 0] = inouts\<^sub>v' x
          latch (x-1) = 1 \<longrightarrow> [0, 0] = inouts\<^sub>v' x
        count(x-1)+1 \<le> 200
          [0, 0] = inouts\<^sub>v' x
      door_close(x)
        [0, 0] = inouts\<^sub>v' x
    count(x-2)+1 \<le> 200
      door_open(x)
        count(x-1)+1 > 200
          latch x = 1 \<longrightarrow> [1, 1] = inouts\<^sub>v' x
          latch x = 0 \<longrightarrow> [0, 0] = inouts\<^sub>v' x
        count(x-1)+1 \<le> 200
          [0, 0] = inouts\<^sub>v' x
      door_close(x)
        [0, 0] = inouts\<^sub>v' x
  door_closed(x-1)  
    door_open(x)
      count(x-1)+1 > 200
        latch x = 1 \<longrightarrow> [1, 1] = inouts\<^sub>v' x
        latch x = 0 \<longrightarrow> [0, 0] = inouts\<^sub>v' x
      count(x-1)+1 \<le> 200
        [0, 0] = inouts\<^sub>v' x
    door_close(x)
      [0, 0] = inouts\<^sub>v' x
*)
(*
  In order to prove 
    inouts\<^sub>v' (Suc (Suc (200 + (x + xa)))) = [1,1]
  we need to prove
    1. (Suc (Suc (200 + (x + xa)))) > 1
    2. door_open (x-1)
       (Suc (200 + (x + xa)))
    3. count(x-2)+1 \<le> 200
       vT_fd_sol_1@(200 + (x + xa)) = 198+1 < 200
    4. door_open (x)
       (Suc (Suc (200 + (x + xa))))
    5. latch(x) = 1
*)
    assume a3: "inouts\<^sub>v x!3 = 1"
    assume a4: "inouts\<^sub>v x!2 = 4"
    assume a5: "inouts\<^sub>v x!0 = 1"
    assume a6: "inouts\<^sub>v (Suc x)!3 = 1"
    assume a7: "inouts\<^sub>v (Suc x)!2 = 8"
    assume a8: "inouts\<^sub>v (Suc x)!0 = 1"
    assume a81: "\<forall>x. hd (tl (inouts\<^sub>v' x)) = inouts\<^sub>v x!(4)"
    assume a9: "\<forall>xb\<le>200. inouts\<^sub>v (Suc (Suc (x + xa + xb)))!0 = 0"
    assume a10: "\<forall>xb\<le>xa + 200. inouts\<^sub>v (Suc (Suc (x + xb)))!(3) = 1 \<and> inouts\<^sub>v (Suc (Suc (x + xb)))!(2) = 8"
    assume a11: "inouts\<^sub>v (Suc (x + xa))!0 = 1"
    assume a12: "\<forall>xb<xa. hd (inouts\<^sub>v' (Suc (Suc (x + xb)))) = 0"
    have len_inouts: "\<forall>x. length(inouts\<^sub>v x) = 5"
      using a2 by blast
    (* rewrite of a11 *)
    have a11': "hd(inouts\<^sub>v (Suc (x + xa))) = 1"
      using a11 len_inouts 
      by (metis hd_conv_nth list.size(3) zero_neq_numeral)
    (* door_open_time is constant *)
    from a1 have a1': "\<forall>x. inouts\<^sub>v x!(Suc 0) = c_door_open_time"
      by simp
    have 1: "\<forall>x::nat. (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) = 200)"
      using a1' by (simp add: RoundZero_def int32_def)
    have 11: "\<forall>x::nat. (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>))) = 200)"
      using a1' by (simp add: RoundZero_def int32_def)
    (* variableTimer at q=0 is 1 *)
    have 12: "(vT_fd_sol_1
              (\<lambda>n1. real_of_int
                     (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
              (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (Suc (Suc (x + xa)))) = 1"
      proof -
        have 1: "(vT_fd_sol_1
              (\<lambda>n1. real_of_int
                     (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
              (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (Suc (Suc (x + xa)))) =
              (vT_fd_sol_1
              (\<lambda>n1. 200)
              (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (Suc (Suc (x + xa))))"
          using 11 by simp
        then have 2: "... = 1"
          apply (simp)
          using a9 a11 by (smt Nat.add_0_right a1 a2 hd_conv_nth le0 list.size(3) zero_less_Suc zero_neq_numeral)
        show ?thesis
          using 1 2 by (simp)
      qed
    (* variableTimer at q is (q+1) *)
    have 13: "\<forall>q<200 . (vT_fd_sol_1
              (\<lambda>n1. real_of_int
                     (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
              (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (Suc (Suc (x + xa + q)))) = q + 1"
      apply (rule allI)
      proof -
        fix q::nat
        have 1: "q < 200 \<longrightarrow> 
          (vT_fd_sol_1 
          (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
          (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (Suc (Suc (x + xa + q))))
           = real (q + 1)"
          proof (induct q)
            case 0
            then show ?case using 12 by simp
          next
            case (Suc q)
            then show ?case
              apply (clarify)
              apply (simp)
              apply (rule conjI)
              apply (clarify)
              using "11" apply auto[1]
              proof -
                assume a1: "q < 199"
                have a1': "Suc q < 200"
                  using a1 by simp
                have 1: "hd (inouts\<^sub>v (Suc (Suc (Suc (x + xa + q))))) = (inouts\<^sub>v (Suc (Suc (Suc (x + xa + q)))))!0"
                  using len_inouts
                  by (metis Suc_numeral Zero_not_Suc hd_conv_nth list.size(3) semiring_norm(5))
                then have 2: "... = (inouts\<^sub>v (Suc (Suc (x + xa + Suc q))))!0"
                  by (smt add_Suc_right)
                then have 3: "... = 0"
                proof -
                  show ?thesis
                    using a1' a9 le_eq_less_or_eq by presburger
                qed
                show "hd (inouts\<^sub>v (Suc (Suc (Suc (x + xa + q))))) = 0"
                  using "1" "2" "3" by linarith
              qed
          qed
        show "q < 200 \<longrightarrow> vT_fd_sol_1 
          (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
          (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (Suc (Suc (x + xa + q))) = real (q + 1)"
          using 1 by linarith
      qed
    have 130: "\<forall>q<200 . (vT_fd_sol_1 (\<lambda>n1. 200)
              (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (Suc (Suc (x + xa + q)))) = q + 1"
      using 13 by (simp add: 11)
    (* variableTimer at previous step of q=0 is 0 *)
    have 14: "(vT_fd_sol_1 (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
               (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (Suc (x + xa))) = 0"
      using a11 a11' 1 11 by (simp)
    (****** The output from m to q=199 is 0 *******)
    (* the output at both m and m+1 is 0 *)
    have output_at_x: "hd (inouts\<^sub>v' x) = 0"
      using a5 a2
      by (smt "1" hd_Cons_tl hd_conv_nth list.inject list.size(3) neq0_conv zero_neq_numeral)
    have output_at_x_1: "hd (inouts\<^sub>v' (Suc x)) = 0"
      using a8 a2 
      by (smt "1" hd_Cons_tl hd_conv_nth list.inject list.size(3) neq0_conv zero_neq_numeral)
    (* the output from m+2 to q=0 is 0 according to a12 a81 *)
    (* the output from q=0 to q=199 is 0 *)
    have output_at_q: "\<forall>q<200 . hd (inouts\<^sub>v' (Suc (Suc (x + xa + q)))) = 0"
      apply (rule allI)
      proof -
        fix q::nat
        have count_less: "\<forall>q<200. 
              (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v  (Suc (Suc (x + xa + q)))!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int
                               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0)  (Suc (x + xa + q)))
                   (real_of_int
                     (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (Suc (x + xa + q))!(Suc 0)) 0\<rceil>)))) +
                  1)"
          apply (rule allI)
          proof -
            fix q::nat
            show 1: "q < 200 \<longrightarrow>
             \<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (Suc (Suc (x + xa + q)))!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (Suc (x + xa + q)))
                   (real_of_int
                     (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (Suc (x + xa + q))!(Suc 0)) 0\<rceil>)))) +
                  1"
              proof (induct q)
                case 0
                then show ?case 
                  using 1 11 14 a11 by simp
              next
                case (Suc q)
                then show ?case 
                  using 1 11 14 a11 13 by simp
              qed
          qed
        show "q < 200 \<longrightarrow> hd (inouts\<^sub>v' (Suc (Suc (x + xa + q)))) = 0"
          proof (induct q)
            case 0
            then show ?case
               using a11 1 11 a2 13 count_less
               by (smt "14" Nat.add_0_right One_nat_def diff_Suc_1 list.sel(1) zero_less_Suc)
          next
            case (Suc q)
            then show ?case 
              using count_less 1 11 a2 
              by (smt One_nat_def Suc_lessD a1 diff_Suc_1 zero_less_Suc)
          qed
      qed
    (******** The 4th input (equal to the output) from m to q=199 is 0 too ********)
    have output_eq: "\<forall>x. hd (tl(inouts\<^sub>v' x)) = hd(inouts\<^sub>v' x)"
      using a2 by (smt hd_Cons_tl list.inject not_gr0 tl_Nil)
    have input4_x: "inouts\<^sub>v (x)!4 = 0"
      using output_at_x output_eq by (simp add: a81)
    have input4_x_1: "inouts\<^sub>v (Suc x)!4 = 0"
      using output_at_x_1 output_eq by (simp add: a81)
    have input4_q: "\<forall>q<200. inouts\<^sub>v (Suc (Suc (x + xa + q)))!4 = 0"
      using output_at_q a81 output_eq by auto
    have a12': "\<forall>xb<xa. (inouts\<^sub>v (Suc (Suc (x + xb))))!(4) = 0"
      using a12 a81 using output_eq by auto
    have input4_x_to_q: "\<forall>q::nat . (q < xa \<longrightarrow> inouts\<^sub>v (Suc (Suc (x + q)))!4 = 0) \<and>
        (q \<ge> xa \<and> q < xa + 200 \<longrightarrow> inouts\<^sub>v (Suc (Suc (x + q)))!4 = 0)"
      using input4_q a12' apply (simp)
      apply (rule allI, clarify)
      by (metis (full_types) add_less_cancel_left le_Suc_ex semiring_normalization_rules(25))
    (******** The latch from m+1 to q=200 is 1 too ********)
    (* latch at m+1 is 1 *)
    have latch_m_1: "latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (Suc x) = 1"
      apply (simp)
      using a3 a4 a5 a6 a7 a8
      by (metis hd_conv_nth input4_x len_inouts list.size(3) zero_neq_numeral zero_neq_one)
    (* latch from m+2 to q=200 is 1 *)
    have latch_1_q_200: "\<forall>q \<le> (xa + 200) . latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (Suc (Suc (x+q))) = 1"
      apply (rule allI)
      proof -
        fix q::nat
        show "q \<le> xa + 200 \<longrightarrow>
         latch_rec_calc_output
          (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!(2) = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!(2) = 8 then 0
                else 1)
          (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!(3) = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!(4) = 0 then 0 else 1)
          (Suc (Suc (x + q))) = 1"
          proof (induct q)
            case 0
            then show ?case 
              using a6 input4_x_1 latch_m_1 by auto
          next
            case (Suc q)
            then show ?case 
              proof -
                assume a1: "q \<le> xa + 200 \<longrightarrow>
                  latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!(2) = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!(2) = 8 then 0
                         else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!(3) = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!(4) = 0 then 0 else 1)
                   (Suc (Suc (x + q))) = 1"
                have 1: "Suc q \<le> xa + 200 \<longrightarrow>
                  ((latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!(2) = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!(2) = 8 then 0
                         else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!(3) = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!(4) = 0 then 0 else 1)
                   (Suc (Suc (x + Suc q)))) = (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!(2) = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!(2) = 8 then 0
                         else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!(3) = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!(4) = 0 then 0 else 1)
                   (Suc (Suc (x + q)))))"
                  apply (clarify)
                  proof -
                    assume a1: "Suc q \<le> xa + 200"
                    have 1: "(\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!(2) = 4 \<longrightarrow> 
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!(2) = 8 then 0 else 1) 
                       (Suc (Suc (x + Suc q))) = 0"
                      using a10 a1 by auto
                    have 2: "(\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!(3) = 0 \<and> 
                              inouts\<^sub>v (n1 - Suc 0)!(4) = 0 then 0 else 1) 
                        (Suc (Suc (x + Suc q))) = 0"
                      apply (simp)
                      apply (rule conjI)
                      using a10 apply (smt Suc_leD a1)
                      using input4_x_to_q a1
                      by (metis Suc_le_eq le_eq_less_or_eq nat_le_linear)
                    show "((latch_rec_calc_output
                       (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!(2) = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!(2) = 8 then 0
                             else 1)
                       (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!(3) = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!(4) = 0 then 0 else 1)
                       (Suc (Suc (x + Suc q)))) = (latch_rec_calc_output
                       (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!(2) = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!(2) = 8 then 0
                             else 1)
                       (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!(3) = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!(4) = 0 then 0 else 1)
                       (Suc (Suc (x + q)))))"
                      using 1 2 by (smt add_Suc_right latch_rec_calc_output.simps(2))
                  qed
                  
                show "Suc q \<le> xa + 200 \<longrightarrow>
                  latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!(2) = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!(2) = 8 then 0
                         else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!(3) = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!(4) = 0 then 0 else 1)
                   (Suc (Suc (x + Suc q))) = 1"
                using 1 a1 by linarith
              qed
          qed
      qed
    have latch_at_202: 
      "latch_rec_calc_output 
         (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                  hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
               then 0 else 1)
         (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
               then 0 else 1) (202 + (x + xa)) = 1"
      proof -
        have 1: "latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (Suc (Suc (x+xa+200))) = 1"
          using latch_1_q_200
          by (metis (no_types, lifting) add.assoc add_le_cancel_left add_less_cancel_left mono_nat_linear_lb)
        have 2: "(Suc (Suc (x+xa+200))) = (202 + (x + xa))"
          by auto
        show ?thesis
          using 1 2 by simp
      qed
  (* variableTime at q=199 is ((198+1)+1), it (\not 200 < 200) *)
    have count_at_198: 
      "vT_fd_sol_1 (\<lambda>n1. 200) (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (200 + (x + xa)) = 199"
      proof -
        have 1: "vT_fd_sol_1 (\<lambda>n1. 200) (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) 
                (Suc (Suc (x + xa + 198))) = 199"
          using 130 by (metis (no_types, lifting) Suc_numeral less_add_Suc2 numeral_Bit0 numeral_Bit1 
              of_nat_numeral one_plus_numeral semiring_norm(3) semiring_norm(5) semiring_norm(8))
        have 2: "(200 + (x + xa)) = (Suc (Suc (x + xa + 198)))"
          by auto
        show ?thesis
          using 1 2 by presburger
      qed
    have count_at_199: 
      "vT_fd_sol_1 (\<lambda>n1. 200) (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (201 + (x + xa)) = 200"
      proof -
        have 1: "vT_fd_sol_1 (\<lambda>n1. 200) (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) 
                (Suc (Suc (x + xa + 199))) = 200"
          using 130
          by (metis Suc_numeral lessI numeral_plus_one of_nat_numeral semiring_norm(5) semiring_norm(8))
        have 2: "(201 + (x + xa)) = (Suc (Suc (x + xa + 199)))"
          by auto
        show ?thesis
          using 1 2 by presburger
      qed
    (* latch (202 + (x + xa)) = 1 and vt (202 + (x + xa)) = 1
       latch (201 + (x + xa)) = 1 and vt (201 + (x + xa)) = 0
    *)
    (* input at q=199 is equal to 0*)
    have "inouts\<^sub>v (Suc (Suc (x + xa + 199)))!0 = 0"
      using a9 len_inouts
      by (metis Suc_numeral le_eq_less_or_eq lessI semiring_norm(5) semiring_norm(8))
    then have "hd(inouts\<^sub>v (Suc (Suc (x + xa + 199)))) = 0"
      using a9 len_inouts by (smt hd_conv_nth list.size(3) zero_neq_numeral)
    then have a9_199: "hd (inouts\<^sub>v (201 + (x + xa))) = 0"
      by (simp add: semiring_normalization_rules(25))
    (* input at q=200 is equal to 0*)
    have a9_200_0: "inouts\<^sub>v (Suc (Suc (x + xa + 200)))!0 = 0"
      using a9 len_inouts by blast
    then have "hd(inouts\<^sub>v (Suc (Suc (x + xa + 200)))) = 0"
      using a9 len_inouts by (smt hd_conv_nth list.size(3) zero_neq_numeral)
    then have a9_200: "hd(inouts\<^sub>v (202 + (x + xa))) = 0"
      by (simp add: semiring_normalization_rules(25))
    have output_at_p_200_imply: "(?P (Suc (Suc (x + xa + 200)))) \<longrightarrow> (inouts\<^sub>v' (202 + (x + xa)) = [1,1])"
      apply (simp)
      apply (simp add: a9_199)
      apply (simp add: 1 11)
      apply (simp add: count_at_198)
      apply (simp add: a9_200)
      apply (simp add: count_at_199)
      by (simp add: latch_at_202)
    have output_at_p_200: "(?P (Suc (Suc (x + xa + 200))))"
      using a2 by smt
    show "inouts\<^sub>v' (202 + (x + xa)) = [1,1]"
      using output_at_p_200 output_at_p_200_imply by fastforce
  qed

text {* Secondly to verify the refinement relation for the feedback. *} 
lemma req_01_ref: "req_01_1_contract f\<^sub>D (4, 1) \<sqsubseteq> plf_rise1shot_simp f\<^sub>D (4, 1)"
  apply (rule feedback_mono[of 5 2])
  using SimBlock_req_01_1_contract apply (blast)
  using post_landing_finalize_1_simblock apply (blast)
  using req_01_ref_plf_rise1shot apply (blast)
  by (auto)

text {* Thirdly to verify the requirement contract satisfied by the feedback of @{text "req_01_1_contract"}. *} 
lemma req_01_fd_ref: 
  "req_01_contract \<sqsubseteq> req_01_1_contract f\<^sub>D (4, 1)"
  using inps_req_01_1_contract outps_req_01_1_contract apply (simp add: PreFD_def PostFD_def)
  proof -
    show "req_01_contract \<sqsubseteq> (\<^bold>\<exists> x \<bullet> (true \<turnstile>\<^sub>n
             (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>4\<guillemotright> \<and> #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>5\<guillemotright> \<and> $inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>f_PreFD x 4\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>n\<guillemotright>)\<^sub>a)) ;;
            req_01_1_contract ;;
            (true \<turnstile>\<^sub>n
             (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>2\<guillemotright> \<and>
                     #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>Suc 0\<guillemotright> \<and>
                     $inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>f_PostFD (Suc 0)\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>n\<guillemotright>)\<^sub>a \<and> \<guillemotleft>uapply\<guillemotright>($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a(\<guillemotleft>Suc 0\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>x n\<guillemotright>)))"
      apply (simp (no_asm) add: req_01_1_contract_def req_01_contract_def)
      (* apply (simp add: ndesign_composition_wp) *)
      apply (rel_simp)
      apply (simp add: f_PostFD_def f_PreFD_def)
      proof -
        fix ok\<^sub>v::bool and inouts\<^sub>v::"nat\<Rightarrow>real list" and
            ok\<^sub>v'::bool and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::"nat\<Rightarrow>real" and
            ok\<^sub>v''::bool and  inouts\<^sub>v''::"nat\<Rightarrow>real list" and ok\<^sub>v'''::bool and 
            inouts\<^sub>v'''::"nat\<Rightarrow>real list"
        assume a1: "(\<forall>xa. (hd (inouts\<^sub>v xa @ [x xa]) = 0 \<or> hd (inouts\<^sub>v xa @ [x xa]) = 1) \<and>
              (inouts\<^sub>v xa @ [x xa])!(Suc 0) = c_door_open_time \<and> 
              ((inouts\<^sub>v xa @ [x xa])!3 = 0 \<or> (inouts\<^sub>v xa @ [x xa])!3 = 1)) \<longrightarrow>
         ok\<^sub>v''' \<and>
         (\<forall>x. length(inouts\<^sub>v''' x) = 2) \<and>
         (\<forall>xa. (inouts\<^sub>v xa @ [x xa])!3 = 1 \<and>
             (inouts\<^sub>v xa @ [x xa])!2 = 4 \<and>
             (inouts\<^sub>v xa @ [x xa])!0 = 1 \<and>
             (inouts\<^sub>v (Suc xa) @ [x (Suc xa)])!3 = 1 \<and>
             (inouts\<^sub>v (Suc xa) @ [x (Suc xa)])!2 = 8 \<and>
             (inouts\<^sub>v (Suc xa) @ [x (Suc xa)])!0 = 1 \<and> (\<forall>xa. hd (tl(inouts\<^sub>v''' xa)) = (inouts\<^sub>v xa @ [x xa])!4) \<longrightarrow>
             (\<forall>xb. (\<forall>xc\<le>200. (inouts\<^sub>v (Suc (Suc (xa + xb + xc))) @ [x (Suc (Suc (xa + xb + xc)))])!0 = 0) \<and>
                   (\<forall>xc\<le>xb + 200.
                       (inouts\<^sub>v (Suc (Suc (xa + xc))) @ [x (Suc (Suc (xa + xc)))])!3 = 1 \<and>
                       (inouts\<^sub>v (Suc (Suc (xa + xc))) @ [x (Suc (Suc (xa + xc)))])!2 = 8) \<and>
                   (inouts\<^sub>v (Suc (xa + xb)) @ [x (Suc (xa + xb))])!0 = 1 \<and>
                   (\<forall>xc<xb. hd (inouts\<^sub>v''' (Suc (Suc (xa + xc)))) = 0) \<longrightarrow>
                   inouts\<^sub>v''' (202 + (xa + xb)) = [1, 1]))"
        assume a2: "ok\<^sub>v''' \<longrightarrow>
           ok\<^sub>v' \<and>
           (\<forall>xa. length(inouts\<^sub>v''' xa) = 2 \<and>
                 length(inouts\<^sub>v' xa) = Suc 0 \<and>
                 inouts\<^sub>v' xa = take (Suc 0) (inouts\<^sub>v''' xa) @ drop (Suc (Suc 0)) (inouts\<^sub>v''' xa) 
            \<and> inouts\<^sub>v''' xa!(Suc 0) = x xa) "
        assume a3: "\<forall>x. (hd (inouts\<^sub>v x) = 0 \<or> hd (inouts\<^sub>v x) = 1) \<and>
           inouts\<^sub>v x!(Suc 0) = c_door_open_time \<and> (inouts\<^sub>v x!3 = 0 \<or> inouts\<^sub>v x!3 = 1)"
        assume a4: "\<forall>xa. length(inouts\<^sub>v xa) = 4 \<and> length(inouts\<^sub>v'' xa) = 5 \<and> 
           inouts\<^sub>v'' xa = take 4 (inouts\<^sub>v xa) @ x xa # drop 4 (inouts\<^sub>v xa)"
        from a4 have 1: "\<forall>xa. length(inouts\<^sub>v xa) = 4"
          by blast
        have 2: "(\<forall>xa. (((hd (inouts\<^sub>v xa @ [x xa]) = 0 \<or> hd (inouts\<^sub>v xa @ [x xa]) = 1) \<and>
              (inouts\<^sub>v xa @ [x xa])!(Suc 0) = c_door_open_time \<and> 
              ((inouts\<^sub>v xa @ [x xa])!3 = 0 \<or> (inouts\<^sub>v xa @ [x xa])!3 = 1))
          = ((hd (inouts\<^sub>v xa) = 0 \<or> hd (inouts\<^sub>v xa) = 1) \<and>
           inouts\<^sub>v xa!(Suc 0) = c_door_open_time \<and> (inouts\<^sub>v xa!3 = 0 \<or> inouts\<^sub>v xa!3 = 1))))"
          using 1
          by (metis Suc_mono Suc_numeral hd_append2 length_greater_0_conv nth_append numeral_2_eq_2 
              numeral_3_eq_3 semiring_norm(2) semiring_norm(8) zero_less_Suc)
        have 3: "ok\<^sub>v'''"
          using 2 a3 a1 by simp
        have 4: "ok\<^sub>v'"
          using a2 3 by blast
        have 5: "\<forall>xa. inouts\<^sub>v' xa = [hd (inouts\<^sub>v''' xa)]"
          using 3 a2 by (metis append_eq_conv_conj length_Cons list.size(3) list_equal_size2 self_append_conv)
        have 6: "\<forall>xa. inouts\<^sub>v''' xa!(Suc 0) = x xa"
          using a2 3 by blast
        have input_at_3: "\<forall>xa. (inouts\<^sub>v xa @ [x xa])!3 = inouts\<^sub>v xa!3"
          using 1 by (simp add: nth_append)
        have input_at_2: "\<forall>xa. (inouts\<^sub>v xa @ [x xa])!2 = inouts\<^sub>v xa!2"
          using 1 by (simp add: nth_append)
        have input_at_1: "\<forall>xa. (inouts\<^sub>v xa @ [x xa])!1 = inouts\<^sub>v xa!1"
          using 1 by (simp add: nth_append)
        have input_at_0: "\<forall>xa. (inouts\<^sub>v xa @ [x xa])!0 = inouts\<^sub>v xa!0"
          using 1 by (simp add: nth_append)
        have input_at_4: "\<forall>xa. (inouts\<^sub>v xa @ [x xa])!4 = x xa"
          using 1 by (simp add: nth_append)
        have feedback: "(\<forall>xa. hd (tl(inouts\<^sub>v''' xa)) = (inouts\<^sub>v xa @ [x xa])!4) = 
              (\<forall>xa. (inouts\<^sub>v''' xa)!(Suc 0) = (x xa))"
          by (metis "3" One_nat_def a2 diff_Suc_1 hd_conv_nth input_at_4 length_greater_0_conv 
              length_tl nth_tl numeral_2_eq_2 zero_less_one)
        have a1': "
         (\<forall>x. length(inouts\<^sub>v''' x) = 2) \<and>
         (\<forall>xa. (inouts\<^sub>v xa)!3 = 1 \<and>
             (inouts\<^sub>v xa)!2 = 4 \<and>
             (inouts\<^sub>v xa)!0 = 1 \<and>
             (inouts\<^sub>v (Suc xa))!3 = 1 \<and>
             (inouts\<^sub>v (Suc xa))!2 = 8 \<and>
             (inouts\<^sub>v (Suc xa))!0 = 1 \<and> (\<forall>xa. (inouts\<^sub>v''' xa)!(Suc 0) = (x xa)) \<longrightarrow>
             (\<forall>xb. (\<forall>xc\<le>200. (inouts\<^sub>v (Suc (Suc (xa + xb + xc))))!0 = 0) \<and>
                   (\<forall>xc\<le>xb + 200.
                       (inouts\<^sub>v (Suc (Suc (xa + xc))))!3 = 1 \<and>
                       (inouts\<^sub>v (Suc (Suc (xa + xc))))!2 = 8) \<and>
                   (inouts\<^sub>v (Suc (xa + xb)))!0 = 1 \<and>
                   (\<forall>xc<xb. hd (inouts\<^sub>v''' (Suc (Suc (xa + xc)))) = 0) \<longrightarrow>
                   inouts\<^sub>v''' (202 + (xa + xb)) = [1, 1]))"
          using input_at_0 input_at_1 input_at_2 input_at_3 input_at_4 a1 6 2 3 a3 feedback 
          by simp
        show "ok\<^sub>v' \<and>
           (\<forall>x. length(inouts\<^sub>v' x) = Suc 0) \<and>
           (\<forall>x. inouts\<^sub>v x!3 = 1 \<and>
                inouts\<^sub>v x!2 = 4 \<and> inouts\<^sub>v x!0 = 1 \<and> inouts\<^sub>v (Suc x)!3 = 1 \<and> 
                inouts\<^sub>v (Suc x)!2 = 8 \<and> inouts\<^sub>v (Suc x)!0 = 1 \<longrightarrow>
                (\<forall>xa. (\<forall>xb\<le>200. inouts\<^sub>v (Suc (Suc (x + xa + xb)))!0 = 0) \<and>
                      (\<forall>xb\<le>xa + 200. inouts\<^sub>v (Suc (Suc (x + xb)))!3 = 1 \<and> inouts\<^sub>v (Suc (Suc (x + xb)))!2 = 8) \<and>
                      inouts\<^sub>v (Suc (x + xa))!0 = 1 \<and> (\<forall>xb<xa. hd (inouts\<^sub>v' (Suc (Suc (x + xb)))) = 0) \<longrightarrow>
                      inouts\<^sub>v' (202 + (x + xa)) = [1]))"
          apply (rule conjI)
          using 4 apply (simp)
          apply (rule conjI)
          using 3 a2 apply blast
          apply (rule allI, clarify)
          using a1' apply (auto)
          by (simp add: "5" "6")
    qed
  qed

text {* Finally, the requirement is held for the @{text "post_landing_finalize_1"} 
  because of transitivity of refinement relation. *}
lemma req_01:
  "req_01_contract \<sqsubseteq> post_landing_finalize_1"
  apply (simp only: post_landing_finalize_1_simp)
  using req_01_fd_ref req_01_ref by auto

subsubsection {* Requirement 02 \label{ssec:plf_req2} *}
text {* @{text "post_landing_finalize_req_02"}: A finalize event is broadcast only once while the 
aircraft is on the ground. *}

text {* @{text "req_02_contract"} is the requirement to be verified. 
Its precondition is the same as @{text "req_01_contract"}. 
Its postcondition specifies that 
\begin{itemize}
  \item it always has four inputs and one output;
  \item the requirement: 
     \begin{itemize}
        \item if a finalize event has been broadcast at step $m$,
        \item while the aircraft is on ground: @{text "ac_on_ground"} is true and @{text "mode=GROUND"},
        \item then a finalize event won't be broadcast again.
     \end{itemize}
\end{itemize}
*}
definition "req_02_contract \<equiv> ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. 
        (
          (hd(x n) = 0 \<or> hd(x n) = 1) \<and> (* door_closed is boolean *)
          ((x n)!1 = c_door_open_time) \<and> (* door_open_time *)
          ((x n)!3 = 0 \<or> (x n)!3 = 1) (* ac_on_ground is boolean *)
        ))\<guillemotright> (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred)
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>4\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>1\<guillemotright>)) \<and>
      (* m    : finalize_event
         ...  : mode is GROUND and ac_on_ground is true
         p    : mode is GROUND and ac_on_ground is true \<Rightarrow> \<not>finalize_event 
      *)
      (\<^bold>\<forall> m::nat \<bullet>
        (
         (head\<^sub>u($inouts\<acute> (\<guillemotleft>m\<guillemotright>)\<^sub>a) =\<^sub>u 1) (* finalize_event at m *)
         \<Rightarrow>
         (
            \<^bold>\<forall> p::nat \<bullet> 
              (
                (\<^bold>\<forall> q::nat \<bullet> ((\<guillemotleft>q\<guillemotright> \<le>\<^sub>u \<guillemotleft>p\<guillemotright>) \<Rightarrow> 
                      ((\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+1+q\<guillemotright>)\<^sub>a)\<^sub>a (3)\<^sub>a =\<^sub>u 1) (* ac_on_ground = true *) \<and>
                       (\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+1+q\<guillemotright>)\<^sub>a)\<^sub>a (2)\<^sub>a =\<^sub>u 8) (* mode = GROUND *)))
                ) (* the aircraft is always on the ground from m+1 to m+1+p *)
                \<Rightarrow> ($inouts\<acute> (\<guillemotleft>m+1+p\<guillemotright>)\<^sub>a) =\<^sub>u \<langle>0\<rangle>(* then the finalize_event is false. *)
              )
         )
      ))))"

text {* @{text "req_02_1_contract"} is the contract for @{text "post_landing_finalize_1"} 
  without feedback: @{text "plf_rise1shot_simp"}. It is similar to @{text "req_02_contract"} except
that 1) it has five inputs and two outputs (the feedback operator will remove one input and one 
output); 2) the 2nd output is equal to the 4th input since they are connected together by 
the feedback loop.
*}
definition "req_02_1_contract \<equiv> ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. 
        (
          (hd(x n) = 0 \<or> hd(x n) = 1) \<and> (* door_closed is boolean *)
          ((x n)!1 = c_door_open_time) \<and> (* door_open_time *)
          ((x n)!3 = 0 \<or> (x n)!3 = 1) (* ac_on_ground is boolean *)
        ))\<guillemotright> (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred)
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>5\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>2\<guillemotright>)) \<and>
      (* m    : finalize_event
         ...  : mode is GROUND and ac_on_ground is true
         p    : mode is GROUND and ac_on_ground is true \<Rightarrow> \<not>finalize_event 
      *)
      (\<^bold>\<forall> m::nat \<bullet>
        (
         (head\<^sub>u($inouts\<acute> (\<guillemotleft>m\<guillemotright>)\<^sub>a) =\<^sub>u 1) (* finalize_event at m *) \<and> 
         (\<^bold>\<forall>n::nat \<bullet> (head\<^sub>u(tail\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a (4)\<^sub>a))
         \<Rightarrow>
         (
            \<^bold>\<forall> p::nat \<bullet> 
              (
                (\<^bold>\<forall> q::nat \<bullet> ((\<guillemotleft>q\<guillemotright> \<le>\<^sub>u \<guillemotleft>p\<guillemotright>) \<Rightarrow> 
                      ((\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+1+q\<guillemotright>)\<^sub>a)\<^sub>a (3)\<^sub>a =\<^sub>u 1) (* ac_on_ground = true *) \<and>
                       (\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>m+1+q\<guillemotright>)\<^sub>a)\<^sub>a (2)\<^sub>a =\<^sub>u 8) (* mode = GROUND *)))
                ) (* the aircraft is always on the ground from m+1 to m+1+p *)
                \<Rightarrow> ($inouts\<acute> (\<guillemotleft>m+1+p\<guillemotright>)\<^sub>a) =\<^sub>u \<langle>0,0\<rangle>(* then the finalize_event is false. *)
              )
         )
      ))))"

lemma SimBlock_req_02_1_contract:
  "SimBlock 5 2 req_02_1_contract"
  apply (simp add: SimBlock_def req_02_1_contract_def)
  apply (rel_auto)
  apply (rule_tac x = "\<lambda>na. [1, 20, if na = 1 then 8 else 4, 1, 0]" in exI)
  apply (rule conjI, simp)
  apply (rule_tac x = "\<lambda>na. [0, 0]" in exI)
  by (simp)
  
lemma inps_req_02_1_contract:
  "inps req_02_1_contract = 5"
  using SimBlock_req_02_1_contract inps_P by blast

lemma outps_req_02_1_contract:
  "outps req_02_1_contract = 2"
  using SimBlock_req_02_1_contract outps_P by blast

text {* In order to verify this requirement, firstly to verify the contract 
 @{text "req_02_1_contract"} refined by @{text "plf_rise1shot_simp"}. *}  
lemma req_02_ref_plf_rise1shot: "req_02_1_contract \<sqsubseteq> plf_rise1shot_simp"
  apply (simp add: FBlock_def plf_rise1shot_simp_def req_02_1_contract_def)
  apply (rule ndesign_refine_intro)
  apply simp
  apply (unfold upred_defs urel_defs)
  apply (simp add: fun_eq_iff relcomp_unfold OO_def
    lens_defs upred_defs alpha_splits Product_Type.split_beta)?
  apply (transfer)
  apply (simp; safe)
  proof -
    fix inouts\<^sub>v inouts\<^sub>v'::"nat \<Rightarrow> real list" and x::nat and xa::nat
    assume a1: "\<forall>x. (hd (inouts\<^sub>v x) = 0 \<or> hd (inouts\<^sub>v x) = 1) \<and>
           inouts\<^sub>v x!(Suc 0) = c_door_open_time \<and> (inouts\<^sub>v x!3 = 0 \<or> inouts\<^sub>v x!3 = 1)"
    let ?P = "\<lambda>x. (x \<le> Suc 0 \<longrightarrow>
            (hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
              (x = 0 \<longrightarrow> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 1 (real_of_int
                           (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                   1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 1 (real_of_int
                              (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                      1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 2 \<and>
               [0, 0] = inouts\<^sub>v' 0 \<and> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 1 (real_of_int
                           (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                   1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 1 (real_of_int
                              (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                      1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)))))) \<and>
            (\<not> hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (x = 0 \<longrightarrow> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 0 (real_of_int
                           (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                   1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 0 (real_of_int
                              (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                      1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 2 \<and>
               [0, 0] = inouts\<^sub>v' 0 \<and> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 0 (real_of_int
                           (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                   1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 0 (real_of_int
                              (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) +
                      1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                               hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                            then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                            hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                         else 1)
                   x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))))) \<and>
           (\<not> x \<le> Suc 0 \<longrightarrow>
            (hd (inouts\<^sub>v (x - Suc 0)) = 0 \<longrightarrow>
             (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))
              < min (vT_fd_sol_1
                      (\<lambda>n1. real_of_int
                             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                      (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc (Suc 0)))
                 (real_of_int
                   (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc (Suc 0))!(Suc 0)) 0\<rceil>)))) +
                1 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int
                               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int
                     (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int
                                  (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int
                        (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)))) \<and>
             (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))
                 < min (vT_fd_sol_1
                         (\<lambda>n1. real_of_int
                                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                         (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc (Suc 0)))
                    (real_of_int
                      (int32 (RoundZero
                               (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc (Suc 0))!(Suc 0)) 0\<rceil>)))) +
                   1 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int
                               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int
                     (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int
                                  (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int
                        (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))) \<and>
            (\<not> hd (inouts\<^sub>v (x - Suc 0)) = 0 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int
                               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int
                     (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int
                                  (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int
                        (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)))) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int
                               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int
                     (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int
                                  (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int
                        (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                           hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0
                        else 1)
                  x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))))"
    assume a2: "\<forall>x. ?P x"
(*
  In order to prove 
    inouts\<^sub>v' (Suc ()) = [1,1]
  we need to prove
    1. (Suc (Suc (200 + (x + xa)))) > 1
    2. door_open (x-1)
       (Suc (200 + (x + xa)))
    3. count(x-2)+1 \<le> 200
       vT_fd_sol_1@(200 + (x + xa)) = 198+1 < 200
    4. door_open (x)
       (Suc (Suc (200 + (x + xa))))
    5. latch(x) = 1
*)
    assume a3: "hd (inouts\<^sub>v' x) = 1"
    assume a4: " \<forall>x. hd (tl (inouts\<^sub>v' x)) = inouts\<^sub>v x!(4)"
    assume a5: " \<forall>xb\<le>xa. inouts\<^sub>v (Suc (x + xb))!(3) = 1 \<and> inouts\<^sub>v (Suc (x + xb))!(2) = 8"
    have len_inouts: "\<forall>x. length(inouts\<^sub>v x) = 5"
      using a2 by blast
    have output_at_0: "inouts\<^sub>v' 0 = [0,0]"
      using a2 by (smt One_nat_def zero_le_one)
    have output_eq: "\<forall>x. hd (tl(inouts\<^sub>v' x)) = hd(inouts\<^sub>v' x)"
      using a2 by (smt hd_Cons_tl list.inject not_gr0 tl_Nil)
    have input_4_at_m: "inouts\<^sub>v x!(4) = 1"
      using a3 a4 output_eq by simp
    have latch_at_m_1: "latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (Suc (x)) = 0"
      using input_4_at_m a5 by simp
    have latch_m_1_to_p: "\<forall>q\<le>xa . latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (Suc (x+q)) = 0"
      apply (rule allI)
      proof -
        fix q::nat
        show "q \<le> xa \<longrightarrow>
         latch_rec_calc_output
          (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!(2) = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!(2) = 8
                then 0 else 1)
          (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!(3) = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!(4) = 0 then 0 else 1)
          (Suc (x + q)) = 0"
          proof (induct q)
            case 0
            then show ?case 
              using latch_at_m_1 by simp
          next
            case (Suc q)
            then show ?case 
              apply (simp add: latch_rec_calc_output.elims)
              using a5 One_nat_def Suc_leD add_Suc_right diff_Suc_1 by smt
          qed
      qed
    have latch_at_p: "latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow>
                              hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0
                           then 0 else 1)
                     (Suc (x+xa)) = 0"
      using latch_m_1_to_p by blast
    show   "inouts\<^sub>v' (Suc (x + xa)) = inouts\<^sub>v' 0"
      using a2 latch_at_p by (smt output_at_0 zero_less_Suc)
  qed

text {* Secondly to verify the refinement relation for the feedback. *} 
lemma req_02_ref: "req_02_1_contract f\<^sub>D (4, 1) \<sqsubseteq> plf_rise1shot_simp f\<^sub>D (4, 1)"
  apply (rule feedback_mono[of 5 2])
  using SimBlock_req_02_1_contract apply (blast)
  using post_landing_finalize_1_simblock apply (blast)
  using req_02_ref_plf_rise1shot apply (blast)
  by (auto)

text {* Thirdly to verify the requirement contract satisfied by the feedback of @{text "req_02_1_contract"}. *} 
lemma req_02_fd_ref: 
  "req_02_contract \<sqsubseteq> req_02_1_contract f\<^sub>D (4, 1)"
  using inps_req_02_1_contract outps_req_02_1_contract apply (simp add: PreFD_def PostFD_def)
  proof -
    show "req_02_contract \<sqsubseteq> (\<^bold>\<exists> x \<bullet> (true \<turnstile>\<^sub>n
             (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>4\<guillemotright> \<and> #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>5\<guillemotright> \<and> 
                    $inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>f_PreFD x 4\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>n\<guillemotright>)\<^sub>a)) ;;
            req_02_1_contract ;;
            (true \<turnstile>\<^sub>n
             (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>2\<guillemotright> \<and>
                     #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>Suc 0\<guillemotright> \<and>
                     $inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>f_PostFD (Suc 0)\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>n\<guillemotright>)\<^sub>a \<and> 
                    \<guillemotleft>uapply\<guillemotright>($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a(\<guillemotleft>Suc 0\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>x n\<guillemotright>)))"
      apply (simp (no_asm) add: req_02_1_contract_def req_02_contract_def)
      (* apply (simp add: ndesign_composition_wp) *)
      apply (rel_simp)
      apply (simp add: f_PostFD_def f_PreFD_def)
      proof -
        fix ok\<^sub>v::bool and inouts\<^sub>v::"nat\<Rightarrow>real list" and
            ok\<^sub>v'::bool and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::"nat\<Rightarrow>real" and
            ok\<^sub>v''::bool and  inouts\<^sub>v''::"nat\<Rightarrow>real list" and ok\<^sub>v'''::bool and 
            inouts\<^sub>v'''::"nat\<Rightarrow>real list"
        assume a1: "(\<forall>xa. (hd (inouts\<^sub>v xa @ [x xa]) = 0 \<or> hd (inouts\<^sub>v xa @ [x xa]) = 1) \<and>
              (inouts\<^sub>v xa @ [x xa])!(Suc 0) = c_door_open_time \<and> 
              ((inouts\<^sub>v xa @ [x xa])!3 = 0 \<or> (inouts\<^sub>v xa @ [x xa])!3 = 1)) \<longrightarrow>
           ok\<^sub>v''' \<and>
           (\<forall>x. length(inouts\<^sub>v''' x) = 2) \<and>
           (\<forall>xa. hd (inouts\<^sub>v''' xa) = 1 \<and> (\<forall>xa. hd (tl (inouts\<^sub>v''' xa)) = (inouts\<^sub>v xa @ [x xa])!4) \<longrightarrow>
             (\<forall>xb. (\<forall>xc\<le>xb. (inouts\<^sub>v (Suc (xa + xc)) @ [x (Suc (xa + xc))])!3 = 1 \<and>
                             (inouts\<^sub>v (Suc (xa + xc)) @ [x (Suc (xa + xc))])!2 = 8) \<longrightarrow>
                   inouts\<^sub>v''' (Suc (xa + xb)) = [0, 0]))"
        assume a2: "ok\<^sub>v''' \<longrightarrow>
           ok\<^sub>v' \<and>
           (\<forall>xa. length(inouts\<^sub>v''' xa) = 2 \<and>
                 length(inouts\<^sub>v' xa) = Suc 0 \<and>
                 inouts\<^sub>v' xa = take (Suc 0) (inouts\<^sub>v''' xa) @ drop (Suc (Suc 0)) (inouts\<^sub>v''' xa) \<and>
                 inouts\<^sub>v''' xa!(Suc 0) = x xa)"
        assume a3: "\<forall>x. (hd (inouts\<^sub>v x) = 0 \<or> hd (inouts\<^sub>v x) = 1) \<and>
           inouts\<^sub>v x!(Suc 0) = c_door_open_time \<and> (inouts\<^sub>v x!3 = 0 \<or> inouts\<^sub>v x!3 = 1)"
        assume a4: "\<forall>xa. length(inouts\<^sub>v xa) = 4 \<and> length(inouts\<^sub>v'' xa) = 5 \<and> 
           inouts\<^sub>v'' xa = take 4 (inouts\<^sub>v xa) @ x xa # drop 4 (inouts\<^sub>v xa)"
        from a4 have 1: "\<forall>xa. length(inouts\<^sub>v xa) = 4"
          by blast
        have 2: "(\<forall>xa. (((hd (inouts\<^sub>v xa @ [x xa]) = 0 \<or> hd (inouts\<^sub>v xa @ [x xa]) = 1) \<and>
              (inouts\<^sub>v xa @ [x xa])!(Suc 0) = c_door_open_time \<and> 
              ((inouts\<^sub>v xa @ [x xa])!3 = 0 \<or> (inouts\<^sub>v xa @ [x xa])!3 = 1))
          = ((hd (inouts\<^sub>v xa) = 0 \<or> hd (inouts\<^sub>v xa) = 1) \<and>
           inouts\<^sub>v xa!(Suc 0) = c_door_open_time \<and> (inouts\<^sub>v xa!3 = 0 \<or> inouts\<^sub>v xa!3 = 1))))"
          using 1
          by (metis Suc_mono Suc_numeral hd_append2 length_greater_0_conv nth_append numeral_2_eq_2 
              numeral_3_eq_3 semiring_norm(2) semiring_norm(8) zero_less_Suc)
        have 3: "ok\<^sub>v'''"
          using 2 a3 a1 by simp
        have 4: "ok\<^sub>v'"
          using a2 3 by blast
        have 5: "\<forall>xa. inouts\<^sub>v' xa = [hd (inouts\<^sub>v''' xa)]"
          using 3 a2 by (metis append_eq_conv_conj length_Cons list.size(3) list_equal_size2 self_append_conv)
        have 6: "\<forall>xa. inouts\<^sub>v''' xa!(Suc 0) = x xa"
          using a2 3 by blast
        have input_at_3: "\<forall>xa. (inouts\<^sub>v xa @ [x xa])!3 = inouts\<^sub>v xa!3"
          using 1 by (simp add: nth_append)
        have input_at_2: "\<forall>xa. (inouts\<^sub>v xa @ [x xa])!2 = inouts\<^sub>v xa!2"
          using 1 by (simp add: nth_append)
        have input_at_1: "\<forall>xa. (inouts\<^sub>v xa @ [x xa])!1 = inouts\<^sub>v xa!1"
          using 1 by (simp add: nth_append)
        have input_at_0: "\<forall>xa. (inouts\<^sub>v xa @ [x xa])!0 = inouts\<^sub>v xa!0"
          using 1 by (simp add: nth_append)
        have input_at_4: "\<forall>xa. (inouts\<^sub>v xa @ [x xa])!4 = x xa"
          using 1 by (simp add: nth_append)
        have feedback: "(\<forall>xa. hd (tl(inouts\<^sub>v''' xa)) = (inouts\<^sub>v xa @ [x xa])!4) = 
              (\<forall>xa. (inouts\<^sub>v''' xa)!(Suc 0) = (x xa))"
          by (metis "3" One_nat_def a2 diff_Suc_1 hd_conv_nth input_at_4 length_greater_0_conv 
              length_tl nth_tl numeral_2_eq_2 zero_less_one)
        have a1': "(\<forall>x. length(inouts\<^sub>v''' x) = 2) \<and>
           (\<forall>xa. hd (inouts\<^sub>v''' xa) = 1 \<and> (\<forall>xa. hd (tl (inouts\<^sub>v''' xa)) = (inouts\<^sub>v xa @ [x xa])!4) \<longrightarrow>
             (\<forall>xb. (\<forall>xc\<le>xb. (inouts\<^sub>v (Suc (xa + xc)) @ [x (Suc (xa + xc))])!3 = 1 \<and>
                             (inouts\<^sub>v (Suc (xa + xc)) @ [x (Suc (xa + xc))])!2 = 8) \<longrightarrow>
                   inouts\<^sub>v''' (Suc (xa + xb)) = [0, 0]))"
          using feedback a1 6 2 a3 input_at_3 input_at_2 by simp
        show "ok\<^sub>v' \<and>
           (\<forall>x. length(inouts\<^sub>v' x) = Suc 0) \<and>
           (\<forall>x. hd (inouts\<^sub>v' x) = 1 \<longrightarrow>
                (\<forall>xa. (\<forall>xb\<le>xa. inouts\<^sub>v (Suc (x + xb))!3 = 1 \<and> inouts\<^sub>v (Suc (x + xb))!2 = 8) \<longrightarrow>
                      inouts\<^sub>v' (Suc (x + xa)) = [0]))"
          apply (rule conjI)
          using 4 apply (simp)
          apply (rule conjI)
          using 3 a2 apply blast
          apply (rule allI, clarify)
          using a1' by (simp add: "3" "5" a2 feedback input_at_2 input_at_3)
    qed
  qed

text {* Finally, the requirement is held for the @{text "post_landing_finalize_1"} 
  because of transitivity of refinement relation. *}
lemma req_02:
  "req_02_contract \<sqsubseteq> post_landing_finalize_1"
  apply (simp only: post_landing_finalize_1_simp)
  using req_02_fd_ref req_02_ref by auto

subsubsection {* Requirement 03 \label{ssec:plf_req3}*}
text {* @{text "post_landing_finalize_req_03"}: The finalize event will not occur during flight. *}

text {* During flight, @{text "ac_on_ground"} is false. According to Assumption 4 in the paper:  
"@{text "door_closed"} must be true if @{text "ac_on_ground"} is false.", then
@{text "door_closed"} is true during flight. Therefore, this requirement can be verified similarly as
 Requirement 04.
 *}

subsubsection {* Requirement 04 \label{ssec:plf_req4}*}
text {* @{text "post_landing_finalize_req_04"}: The finalize event will not be enabled while the 
aircraft door is closed. *}
(* Methods to prove: Compositional reasoning

** Method 1:
  1. ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. ((hd(x n) = 0 \<or> hd(x n) = 1)))\<guillemotright> 
        (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred) 
      \<turnstile>\<^sub>n
      ((\<^bold>\<forall> n::nat \<bullet> 
        ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>5\<guillemotright>) \<and>
        ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>7\<guillemotright>) \<and>
        (head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) \<and> 
        (head\<^sub>u(tail\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u head\<^sub>u(tail\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a))))
      )) \<sqsubseteq> post_landing_finalize_part1
  2. ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. (hd(x n) = 0 \<or> hd(x n) = 1) \<and> 
        (hd(tl(x n)) \<ge> 0 \<and> hd(tl(x n)) < 214748364))\<guillemotright> 
      (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred)
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>2\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>1\<guillemotright>) \<and>
      (head\<^sub>u(($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0) \<Rightarrow> (head\<^sub>u(($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0))
    )) \<sqsubseteq> post_landing_finalize_part2
  3. ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. (hd(x n) = 0 \<or> hd(x n) = 1) \<and> 
        (hd(tl(x n)) \<ge> 0 \<and> hd(tl(x n)) < 214748364))\<guillemotright> 
      (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred)
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>7\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>2\<guillemotright>) \<and>
      (head\<^sub>u(($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0) \<Rightarrow> (head\<^sub>u(($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0))
    ))  \<sqsubseteq> (post_landing_finalize_part2 \<parallel>\<^sub>B post_landing_finalize_part3)
  4.  (((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. ((hd(x n) = 0 \<or> hd(x n) = 1)))\<guillemotright> 
        (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred) 
      \<turnstile>\<^sub>n
      ((\<^bold>\<forall> n::nat \<bullet> 
        ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>5\<guillemotright>) \<and>
        ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>7\<guillemotright>) \<and>
        (head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) \<and> 
        (head\<^sub>u(tail\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u head\<^sub>u(tail\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a))))
      )) ;; 
      ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. (hd(x n) = 0 \<or> hd(x n) = 1) \<and> 
        (hd(tl(x n)) \<ge> 0 \<and> hd(tl(x n)) < 214748364))\<guillemotright> 
      (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred)
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>7\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>2\<guillemotright>) \<and>
      (head\<^sub>u(($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0) \<Rightarrow> (head\<^sub>u(($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0))
    )))
   \<sqsubseteq> (post_landing_finalize_part1 ;; ( post_landing_finalize_part2 \<parallel>\<^sub>B post_landing_finalize_part3))
  5. ... 

** Method 2:
  1. ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. (
        (hd(x n) = 0 \<or> hd(x n) = 1) \<and> (* door_closed is boolean *)
        ((x n)!1 > 0 \<and> (x n)!1 < 1000) \<and> (* door_open_time *)
        ((x n)!3 = 0 \<or> (x n)!3 = 1) \<and> (* ac_on_ground is boolean *)
        ((x n)!2 = 4 \<or> (x n)!2 = 8)
        ))\<guillemotright> (* mode is either LANDING (4) or GROUND (8) *)
        (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred) 
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>5\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>2\<guillemotright>) \<and>
      (head\<^sub>u(($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) (* door_closed is true *)
        \<Rightarrow> (head\<^sub>u(($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0) \<and> (head\<^sub>u(tail\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0))
    )) \<sqsubseteq> f15
  2. then
    ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. (
        (hd(x n) = 0 \<or> hd(x n) = 1) \<and> (* door_closed is boolean *)
        ((x n)!1 > 0 \<and> (x n)!1 < 1000) \<and> (* door_open_time *)
        ((x n)!3 = 0 \<or> (x n)!3 = 1) \<and> (* ac_on_ground is boolean *)
        ((x n)!2 = 4 \<or> (x n)!2 = 8)
        ))\<guillemotright> (* mode is either LANDING (4) or GROUND (8) *)
        (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred) 
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>5\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>2\<guillemotright>) \<and>
      (head\<^sub>u(($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) (* door_closed is true *)
        \<Rightarrow> (head\<^sub>u(($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0) \<and> (head\<^sub>u(tail\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0))
    )) f\<^sub>D (4, 1) \<sqsubseteq> f15 f\<^sub>D (4, 1)
*)
(*
lemma post_landing_finalize_req_04:
  " ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. (
        (hd(x n) = 0 \<or> hd(x n) = 1) \<and> (* door_closed is boolean *)
        ((x n)!1 > 0 \<and> (x n)!1 < 1000) \<and> (* door_open_time *)
        ((x n)!3 = 0 \<or> (x n)!3 = 1) \<and> (* ac_on_ground is boolean *)
        ((x n)!2 = 4 \<or> (x n)!2 = 8)
        ))\<guillemotright> (* mode is either LANDING (4) or GROUND (8) *)
        (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred) 
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>4\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>1\<guillemotright>) \<and>
      (head\<^sub>u(($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) (* door_closed is true *)
        \<Rightarrow> (head\<^sub>u(($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0))
    )) \<sqsubseteq> post_landing_finalize_1"
  apply (simp (no_asm) add: post_landing_finalize_1_simp)
  apply (simp add: PreFD_def PostFD_def FBlock_def)
  apply (simp add: ndesign_composition_wp)
  apply (simp add: wp_upred_def)
  apply (rel_simp)
sorry
*)

text {* Requirement 4: assumes 
\begin{itemize}
  \item @{text "door_closed"} and @{text "ac_on_ground"} are boolean,
  \item @{text "door_open_time"} is within (0, @{text "max_door_open_time"})
\end{itemize} 
then it must guarantee that 
\begin{itemize}
  \item it has four inputs and one output,
  \item if the door is closed, then the output is always false (0).
\end{itemize} 
*}
abbreviation "req_04_contract \<equiv> ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. (
        (hd(x n) = 0 \<or> hd(x n) = 1) \<and> (* door_closed is boolean *)
        ((x n)!1 > 0 \<and> (x n)!1 < max_door_open_time) \<and> (* door_open_time *)
        ((x n)!3 = 0 \<or> (x n)!3 = 1) (* ac_on_ground is boolean *)
        ))\<guillemotright>
        (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred) 
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>4\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>1\<guillemotright>) \<and>
      ((head\<^sub>u(($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) (* door_closed is true *)
        \<Rightarrow> (head\<^sub>u(($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0)))
    ))"

text {* This is the contract for @{text "post_landing_finalize_1"} without the last feedback. Since 
@{text "post_landing_finalize_1"} is equal to @{text "plf_rise1shot_simp f\<^sub>D (4, 1)"}, then this is 
the contract for @{text "plf_rise1shot_simp"}. *}
definition "req_04_1_contract \<equiv> ((\<^bold>\<forall> n::nat \<bullet> (
      \<guillemotleft>(\<lambda>x n. (
        (hd(x n) = 0 \<or> hd(x n) = 1) \<and> (* door_closed is boolean *)
        ((x n)!1 > 0 \<and> (x n)!1 < max_door_open_time) \<and> (* door_open_time *)
        ((x n)!3 = 0 \<or> (x n)!3 = 1) (* ac_on_ground is boolean *)
        ))\<guillemotright>
        (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred) 
    \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>5\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>2\<guillemotright>) \<and>
      ((head\<^sub>u(($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) (* door_closed is true *)
        \<Rightarrow> (head\<^sub>u(($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0) \<and> (head\<^sub>u(tail\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 0)))
    ))"

lemma SimBlock_req_04_1_contract:
  "SimBlock 5 2 req_04_1_contract"
  apply (simp add: SimBlock_def req_04_1_contract_def)
  apply (rel_auto)
  apply (rule_tac x = "\<lambda>na. [0, 20, 4, 0, 0]" in exI, simp)
  by (rule_tac x = "\<lambda>na. [0, 0]" in exI, simp)
  
lemma inps_req_04_1_contract:
  "inps req_04_1_contract = 5"
  using SimBlock_req_04_1_contract inps_P by blast

lemma outps_req_04_1_contract:
  "outps req_04_1_contract = 2"
  using SimBlock_req_04_1_contract outps_P by blast

text {* In order to verify this requirement, firstly to verify the contract 
 @{text "req_04_1_contract"} refined by @{text "plf_rise1shot_simp"}. *}  
lemma req_04_ref_plf_rise1shot: "req_04_1_contract \<sqsubseteq> plf_rise1shot_simp"
  apply (simp add: FBlock_def plf_rise1shot_simp_def req_04_1_contract_def)
  apply (rule ndesign_refine_intro)
  apply simp
  apply (unfold upred_defs urel_defs)
  apply (simp add: fun_eq_iff relcomp_unfold OO_def
    lens_defs upred_defs alpha_splits Product_Type.split_beta)?
  apply (transfer)
  apply (simp; safe)
  apply (rename_tac inouts\<^sub>v inouts\<^sub>v' x)
  proof -
    fix inouts\<^sub>v inouts\<^sub>v'::"nat \<Rightarrow> real list" and x::nat
    assume a1: "\<forall>x. (hd (inouts\<^sub>v x) = 0 \<or> hd (inouts\<^sub>v x) = 1) \<and>
           0 < inouts\<^sub>v x!(Suc 0) \<and>
           inouts\<^sub>v x!(Suc 0) < max_door_open_time \<and>
           (inouts\<^sub>v x!3 = 0 \<or> inouts\<^sub>v x!3 = 1)"
    assume a2: "\<forall>x. (x \<le> Suc 0 \<longrightarrow>
            (hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
              (x = 0 \<longrightarrow> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 1 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 1 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 2 \<and>
               [0, 0] = inouts\<^sub>v' 0 \<and> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 1 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 1 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)))))) \<and>
            (\<not> hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (x = 0 \<longrightarrow> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 0 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 0 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 2 \<and>
               [0, 0] = inouts\<^sub>v' 0 \<and> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 0 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 0 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))))) \<and>
           (\<not> x \<le> Suc 0 \<longrightarrow>
            (hd (inouts\<^sub>v (x - Suc 0)) = 0 \<longrightarrow>
             (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))
              < min (vT_fd_sol_1
                      (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                      (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc (Suc 0)))
                 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc (Suc 0))!(Suc 0)) 0\<rceil>)))) +
                1 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)))) \<and>
             (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))
                 < min (vT_fd_sol_1
                         (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                         (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc (Suc 0)))
                    (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc (Suc 0))!(Suc 0)) 0\<rceil>)))) +
                   1 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))) \<and>
            (\<not> hd (inouts\<^sub>v (x - Suc 0)) = 0 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)))) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))))"
    assume a3: "hd (inouts\<^sub>v x) = 1"
    have 1: "\<forall>x. (inouts\<^sub>v x!(Suc 0)) > 0 \<and> (inouts\<^sub>v x!(Suc 0)) < max_door_open_time"
      using a1 by blast
    have 2: "\<forall>x. int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) \<ge> 0 \<and> 
          int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < (Rate * max_door_open_time + 1)" 
      apply (rule allI)
      proof -
        fix xx::nat
        have 0: "Rate * max (inouts\<^sub>v xx!(Suc 0)) 0 < Rate * max_door_open_time \<and> Rate * max x 0 \<ge> 0"
          using 1 by simp
        have 1: "\<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil> < (Rate * max (inouts\<^sub>v xx!(Suc 0)) 0 + 1)"
          using ceiling_correct by linarith
        then have "\<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil> < (Rate * max_door_open_time + 1)"
          using 0 1 by linarith
        then have 2: "\<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil> < (Rate * max_door_open_time + 1) \<and> 
                  \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil> \<ge> 0"
          using 0 by (smt ceiling_le_zero ceiling_zero)
        have 3: "real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil> < (Rate * max_door_open_time + 1) \<and> 
                  real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil> \<ge> 0"
          using 2 by (simp)
        have 4: "RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>) 
                      = \<lfloor>real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>\<rfloor>"
          using RoundZero_def by (simp)
        have 5: "RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>) < (Rate * max_door_open_time + 1) \<and> 
                  RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>) \<ge> 0"
          using 3 4 by auto
        have 51: "RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>) < (Rate * 214748364 + 1) \<and> 
                  RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>) \<ge> 0"
          using 5 1 by auto
        have 6: "int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>))
            =  RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>)"
          using 51 int32_eq 1 by simp
        have 7: "int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>)) 
                      < (Rate * max_door_open_time + 1) \<and> 
                  int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>)) \<ge> 0"
          using 5 6 by (simp)
        show "0 \<le> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>)) \<and>
         int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>)) < Rate * max_door_open_time + 1"
          using 7 by blast
      qed
    show "hd (inouts\<^sub>v' x) = 0"
      using 2 a2 a3 a1 neq0_conv list.sel(1) by (smt)
  next
    fix inouts\<^sub>v inouts\<^sub>v'::"nat \<Rightarrow> real list" and x::nat
    assume a1: "\<forall>x. (hd (inouts\<^sub>v x) = 0 \<or> hd (inouts\<^sub>v x) = 1) \<and>
           0 < inouts\<^sub>v x!(Suc 0) \<and>
           inouts\<^sub>v x!(Suc 0) < max_door_open_time \<and>
           (inouts\<^sub>v x!3 = 0 \<or> inouts\<^sub>v x!3 = 1)"
    assume a2: "\<forall>x. (x \<le> Suc 0 \<longrightarrow>
            (hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
              (x = 0 \<longrightarrow> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 1 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 1 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 1 \<longrightarrow>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 2 \<and>
               [0, 0] = inouts\<^sub>v' 0 \<and> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 1 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 1 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)))))) \<and>
            (\<not> hd (inouts\<^sub>v 0) = 0 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (x = 0 \<longrightarrow> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 0 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 0 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (x = 0 \<longrightarrow>
               length(inouts\<^sub>v 0) = 5 \<and>
               length(inouts\<^sub>v' 0) = 2 \<and>
               [0, 0] = inouts\<^sub>v' 0 \<and> length(inouts\<^sub>v 0) = 5 \<and> length(inouts\<^sub>v' 0) = 2 \<and> [0, 0] = inouts\<^sub>v' 0) \<and>
              (0 < x \<longrightarrow>
               (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                 < min 0 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                    < min 0 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v 0!(Suc 0)) 0\<rceil>)))) + 1 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
               (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
                (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 (\<not> latch_rec_calc_output
                      (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                            then 0 else 1)
                      (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                      x =
                     0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
                (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and>
                 length(inouts\<^sub>v' x) = 2 \<and>
                 [0, 0] = inouts\<^sub>v' x \<and>
                 (latch_rec_calc_output
                   (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                         then 0 else 1)
                   (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                  0 \<longrightarrow>
                  length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))))) \<and>
           (\<not> x \<le> Suc 0 \<longrightarrow>
            (hd (inouts\<^sub>v (x - Suc 0)) = 0 \<longrightarrow>
             (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))
              < min (vT_fd_sol_1
                      (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                      (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc (Suc 0)))
                 (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc (Suc 0))!(Suc 0)) 0\<rceil>)))) +
                1 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)))) \<and>
             (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))
                 < min (vT_fd_sol_1
                         (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                         (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc (Suc 0)))
                    (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc (Suc 0))!(Suc 0)) 0\<rceil>)))) +
                   1 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))) \<and>
            (\<not> hd (inouts\<^sub>v (x - Suc 0)) = 0 \<longrightarrow>
             (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<and>
                 latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                  (x - Suc 0) =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x) \<and>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     (x - Suc 0) =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)))) \<and>
             (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
              (hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                < min (vT_fd_sol_1
                        (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                        (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                   (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                  1 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)))
                   < min (vT_fd_sol_1
                           (\<lambda>n1. real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v n1!(Suc 0)) 0\<rceil>))))
                           (\<lambda>n1. if hd (inouts\<^sub>v n1) = 0 then 1 else 0) (x - Suc 0))
                      (real_of_int (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v (x - Suc 0)!(Suc 0)) 0\<rceil>)))) +
                     1 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))) \<and>
              (\<not> hd (inouts\<^sub>v x) = 0 \<longrightarrow>
               (int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                (\<not> latch_rec_calc_output
                     (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                           then 0 else 1)
                     (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1)
                     x =
                    0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [1, 1] = inouts\<^sub>v' x) \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x)) \<and>
               (\<not> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < 0 \<longrightarrow>
                length(inouts\<^sub>v x) = 5 \<and>
                length(inouts\<^sub>v' x) = 2 \<and>
                [0, 0] = inouts\<^sub>v' x \<and>
                (latch_rec_calc_output
                  (\<lambda>n1. if inouts\<^sub>v (n1 - Suc 0)!2 = 4 \<longrightarrow> hd (inouts\<^sub>v n1) = 0 \<or> n1 = 0 \<or> \<not> inouts\<^sub>v n1!2 = 8
                        then 0 else 1)
                  (\<lambda>n1. if n1 = 0 \<or> \<not> inouts\<^sub>v (n1 - Suc 0)!3 = 0 \<and> inouts\<^sub>v (n1 - Suc 0)!4 = 0 then 0 else 1) x =
                 0 \<longrightarrow>
                 length(inouts\<^sub>v x) = 5 \<and> length(inouts\<^sub>v' x) = 2 \<and> [0, 0] = inouts\<^sub>v' x))))))"
    assume a3: "hd (inouts\<^sub>v x) = 1"
    have 1: "\<forall>x. (inouts\<^sub>v x!(Suc 0)) > 0 \<and> (inouts\<^sub>v x!(Suc 0)) < max_door_open_time"
      using a1 by blast
    have 2: "\<forall>x. int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) \<ge> 0 \<and> 
          int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v x!(Suc 0)) 0\<rceil>)) < (Rate * max_door_open_time + 1)" 
      apply (rule allI)
      proof -
        fix xx::nat
        have 0: "Rate * max (inouts\<^sub>v xx!(Suc 0)) 0 < Rate * max_door_open_time \<and> Rate * max x 0 \<ge> 0"
          using 1 by simp
        have 1: "\<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil> < (Rate * max (inouts\<^sub>v xx!(Suc 0)) 0 + 1)"
          using ceiling_correct by linarith
        then have "\<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil> < (Rate * max_door_open_time + 1)"
          using 0 1 by linarith
        then have 2: "\<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil> < (Rate * max_door_open_time + 1) \<and> 
                  \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil> \<ge> 0"
          using 0 by (smt ceiling_le_zero ceiling_zero)
        have 3: "real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil> < (Rate * max_door_open_time + 1) \<and> 
                  real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil> \<ge> 0"
          using 2 by (simp)
        have 4: "RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>) 
                      = \<lfloor>real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>\<rfloor>"
          using RoundZero_def by (simp)
        have 5: "RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>) < (Rate * max_door_open_time + 1) \<and> 
                  RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>) \<ge> 0"
          using 3 4 by auto
        have 51: "RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>) < (Rate * 214748364 + 1) \<and> 
                  RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>) \<ge> 0"
          using 5 1 by auto
        have 6: "int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>))
            =  RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>)"
          using 51 int32_eq 1 by simp
        have 7: "int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>)) 
                      < (Rate * max_door_open_time + 1) \<and> 
                  int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>)) \<ge> 0"
          using 5 6 by (simp)
        show "0 \<le> int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>)) \<and>
         int32 (RoundZero (real_of_int \<lceil>Rate * max (inouts\<^sub>v xx!(Suc 0)) 0\<rceil>)) < Rate * max_door_open_time + 1"
          using 7 by blast
      qed
    show "hd (tl (inouts\<^sub>v' x)) = 0"
      using 2 a2 a3 a1 neq0_conv list.sel(1) list.sel(3) by (smt)
  qed

text {* Secondly to verify the refinement relation for the feedback. *} 
lemma req_04_ref: "req_04_1_contract f\<^sub>D (4, 1) \<sqsubseteq> plf_rise1shot_simp f\<^sub>D (4, 1)"
  apply (rule feedback_mono[of 5 2])
  using SimBlock_req_04_1_contract apply (blast)
  using post_landing_finalize_1_simblock apply (blast)
  using req_04_ref_plf_rise1shot apply (blast)
  by (auto)

text {* Thirdly to verify the requirement contract satisfied by the feedback of @{text "req_04_1_contract"}. *} 
lemma req_04_fd_ref: 
  "req_04_contract \<sqsubseteq> req_04_1_contract f\<^sub>D (4, 1)"
  using inps_req_04_1_contract outps_req_04_1_contract apply (simp add: PreFD_def PostFD_def)
  proof -
    show "(\<^bold>\<forall> n \<bullet> \<guillemotleft>\<lambda>x n. (hd (x n) = 0 \<or> hd (x n) = 1) \<and>
                   0 < x n!(Suc 0) \<and>
                   x n!(Suc 0) < max_door_open_time \<and>
                   (x n!3 = 0 \<or> x n!3 = 1)\<guillemotright>(&inouts)\<^sub>a(\<guillemotleft>n\<guillemotright>)\<^sub>a) \<turnstile>\<^sub>n
          (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>4\<guillemotright> \<and>
                  #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>Suc 0\<guillemotright> \<and> (head\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u 1 \<Rightarrow> head\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u 0)) 
        \<sqsubseteq>
          (\<^bold>\<exists> x \<bullet> (true \<turnstile>\<^sub>n
             (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>4\<guillemotright> \<and>
                     #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>5\<guillemotright> \<and> $inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>f_PreFD x 4\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>n\<guillemotright>)\<^sub>a)) ;;
            req_04_1_contract ;;
            (true \<turnstile>\<^sub>n
             (\<^bold>\<forall> n \<bullet> #\<^sub>u($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>2\<guillemotright> \<and>
                     #\<^sub>u($inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>Suc 0\<guillemotright> \<and>
                     $inouts\<acute>(\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>f_PostFD (Suc 0)\<guillemotright>($inouts)\<^sub>a(\<guillemotleft>n\<guillemotright>)\<^sub>a \<and>
                     \<guillemotleft>uapply\<guillemotright>($inouts(\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a(\<guillemotleft>Suc 0\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>x n\<guillemotright>)))"
      apply (simp (no_asm) add: req_04_1_contract_def)
      (* apply (simp add: ndesign_composition_wp) *)
      apply (rel_simp)
      apply (simp add: f_PostFD_def f_PreFD_def)
      proof -
        fix ok\<^sub>v::bool and inouts\<^sub>v::"nat\<Rightarrow>real list" and
            ok\<^sub>v'::bool and inouts\<^sub>v'::"nat\<Rightarrow>real list" and x::"nat\<Rightarrow>real" and
            ok\<^sub>v''::bool and  inouts\<^sub>v''::"nat\<Rightarrow>real list" and ok\<^sub>v'''::bool and 
            inouts\<^sub>v'''::"nat\<Rightarrow>real list"
        assume a1: "(\<forall>xa. (hd (inouts\<^sub>v xa @ [x xa]) = 0 \<or> hd (inouts\<^sub>v xa @ [x xa]) = 1) \<and>
             0 < (inouts\<^sub>v xa @ [x xa])!(Suc 0) \<and>
             (inouts\<^sub>v xa @ [x xa])!(Suc 0) < max_door_open_time \<and>
             ((inouts\<^sub>v xa @ [x xa])!3 = 0 \<or> (inouts\<^sub>v xa @ [x xa])!3 = 1)) \<longrightarrow>
         ok\<^sub>v''' \<and>
         (\<forall>xa. length(inouts\<^sub>v''' xa) = 2 \<and>
             (hd (inouts\<^sub>v xa @ [x xa]) = 1 \<longrightarrow>
              hd (inouts\<^sub>v''' xa) = 0 \<and> hd (tl (inouts\<^sub>v''' xa)) = 0))"
        assume a2: "ok\<^sub>v''' \<longrightarrow>
         ok\<^sub>v' \<and>
         (\<forall>xa. length(inouts\<^sub>v''' xa) = 2 \<and>
             length(inouts\<^sub>v' xa) = Suc 0 \<and>
             inouts\<^sub>v' xa = take (Suc 0) (inouts\<^sub>v''' xa) @ drop (Suc (Suc 0)) (inouts\<^sub>v''' xa) \<and>
             inouts\<^sub>v''' xa!(Suc 0) = x xa)"
        assume a3: "\<forall>x. (hd (inouts\<^sub>v x) = 0 \<or> hd (inouts\<^sub>v x) = 1) \<and>
           0 < inouts\<^sub>v x!(Suc 0) \<and>
           inouts\<^sub>v x!(Suc 0) < max_door_open_time \<and>
           (inouts\<^sub>v x!3 = 0 \<or> inouts\<^sub>v x!3 = 1)"
        assume a4: "\<forall>xa. length(inouts\<^sub>v xa) = 4 \<and>
            length(inouts\<^sub>v'' xa) = 5 \<and>
            inouts\<^sub>v'' xa = take 4 (inouts\<^sub>v xa) @ x xa # drop 4 (inouts\<^sub>v xa)"
        from a4 have 1: "\<forall>xa. length(inouts\<^sub>v xa) = 4"
          by blast
        have 2: "(\<forall>xa. (((hd (inouts\<^sub>v xa @ [x xa]) = 0 \<or> hd (inouts\<^sub>v xa @ [x xa]) = 1) \<and>
             0 < (inouts\<^sub>v xa @ [x xa])!(Suc 0) \<and>
             (inouts\<^sub>v xa @ [x xa])!(Suc 0) < max_door_open_time \<and>
             ((inouts\<^sub>v xa @ [x xa])!3 = 0 \<or> (inouts\<^sub>v xa @ [x xa])!3 = 1))
          = ((hd (inouts\<^sub>v xa) = 0 \<or> hd (inouts\<^sub>v xa) = 1) \<and>
           0 < inouts\<^sub>v xa!(Suc 0) \<and>
           inouts\<^sub>v xa!(Suc 0) < max_door_open_time \<and>
           (inouts\<^sub>v xa!3 = 0 \<or> inouts\<^sub>v xa!3 = 1))))"
          using 1
          by (metis Suc_mono Suc_numeral hd_append2 length_greater_0_conv nth_append numeral_2_eq_2 
              numeral_3_eq_3 semiring_norm(2) semiring_norm(8) zero_less_Suc)
        have 3: "ok\<^sub>v'''"
          using 2 a3 a1 by simp
        have 4: "(\<forall>xa. length(inouts\<^sub>v''' xa) = 2 \<and>
             (hd (inouts\<^sub>v xa) = 1 \<longrightarrow>
              hd (inouts\<^sub>v''' xa) = 0 \<and> hd (tl (inouts\<^sub>v''' xa)) = 0))"
          using 1 2 a3 a1 by (smt hd_append2 list.size(3) zero_neq_numeral)
        have 5: "\<forall>xa. inouts\<^sub>v' xa = [hd (inouts\<^sub>v''' xa)]"
          using 3 a2 by (metis append_eq_conv_conj length_Cons list.size(3) list_equal_size2 self_append_conv)
        show "ok\<^sub>v' \<and> (\<forall>x. length(inouts\<^sub>v' x) = Suc 0 \<and> (hd (inouts\<^sub>v x) = 1 \<longrightarrow> hd (inouts\<^sub>v' x) = 0))"
          apply (rule conjI)
          using 3 a2 apply blast
          apply (rule allI)
          apply (rule conjI)
          using 3 a2 apply blast
          using 3 a2 4 by (simp add: "5")
    qed
  qed

text {* Finally, the requirement is held for the @{text "post_landing_finalize_1"} 
  because of transitivity of refinement relation. *}
lemma req_04:
  "req_04_contract \<sqsubseteq> post_landing_finalize_1"
  apply (simp only: post_landing_finalize_1_simp)
  using req_04_fd_ref req_04_ref by auto

end