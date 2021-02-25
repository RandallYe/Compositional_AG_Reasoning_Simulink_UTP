section {* Block Theories \label{sec:block_theories} *}
text {* In this section, we define main theories of block diagrams in UTP. *}

theory simu_contract_real
  imports
    "~~/src/HOL/Word/Word"
    utp_designs
begin
(* declare [[ smt_solver = z3 ]] *)
(*
-- {* timeout in seconds *}
declare [[ smt_timeout = 600 ]]
*)
syntax
  "_svid_des"  :: "svid" ("\<^bold>v\<^sub>D")

translations
  "_svid_des" => "\<Sigma>\<^sub>D"

text {* Defined Simulink blocks using designs directly. *}
named_theorems sim_blocks (* definition of blocks *)
text {* Functions used to define Simulink blocks via patterns. *}
named_theorems f_blocks (* functions of blocks *)
text {* Defined Simulink blocks using functions and patterns. *}
named_theorems f_sim_blocks (* functions defined blocks *)
text {* @{text "SimBlock"} healthiness. *}
named_theorems simblock_healthy (* healthy conditions of blocks *)

(* This will remove the grammar ambiguity between conj vs. uconj for \<and> *)
recall_syntax

subsection {* Additional Laws *}
theorem ndesign_composition:
  "((p1 \<turnstile>\<^sub>n Q1) ;; (p2 \<turnstile>\<^sub>n Q2)) = ((p1 \<and> \<not> \<lfloor>Q1 ;; (\<not> \<lceil>p2\<rceil>\<^sub><)\<rfloor>\<^sub><) \<turnstile>\<^sub>n (Q1 ;; Q2))"
  apply (ndes_simp, simp add: wp_upred_def)
  by (rel_simp)

lemma list_equal_size2:
  fixes x
  assumes "length(x) = 2"
  shows "x = [hd(x)]@[last(x)]"
proof -
  have 1: "x = [hd(x)]@tl(x)"
    by (metis append_Cons append_Nil assms hd_Cons_tl length_0_conv zero_not_eq_two)
  have 2: "tl(x) = [last(x)]"
    using assms
    by (metis One_nat_def "1" append_butlast_last_id append_eq_append_conv append_is_Nil_conv 
        cancel_ab_semigroup_add_class.add_diff_cancel_left' length_Cons length_tl list.size(3) 
        nat_1_add_1 not_Cons_self2)
  from 1 and 2 show ?thesis
    by auto
qed

theorem ndesign_refinement:
  "(P1 \<turnstile>\<^sub>n Q1 \<sqsubseteq> P2 \<turnstile>\<^sub>n Q2) \<longleftrightarrow> (`P1 \<Rightarrow> P2` \<and> `\<lceil>P1\<rceil>\<^sub>< \<and> Q2 \<Rightarrow> Q1`)"
  by (rel_auto)

theorem ndesign_refinement':
  "(P1 \<turnstile>\<^sub>n Q1 \<sqsubseteq> P2 \<turnstile>\<^sub>n Q2) \<longleftrightarrow> (P2 \<sqsubseteq> P1 \<and> Q1 \<sqsubseteq> (\<lceil>P1\<rceil>\<^sub>< \<and> Q2))"
  by (meson ndesign_refinement refBy_order)

lemma assume_Ran: "P ;; [Ran(P)]\<^sup>\<top> = P"
  apply (rel_auto)
done

fun sum_list1 where 
"sum_list1 [] = 0" |
"sum_list1 (x#xs) = (sum_list1 xs + x)"

subsection {* State Space *}
text {* @{term "inouts"}: input and output signals, abstracted as a function from step numbers to 
a list of inputs or outputs where we use universal real number as the data type of signals. *}

alphabet sim_state =
  inouts :: "nat \<Rightarrow> real list"

subsection {* Patterns *}
text {* @{text "FBlock"} is a pattern to define a block with precondition, number of inputs, 
number of outputs, and postcondition. *}

definition FBlock :: 
  "((nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 
     nat \<Rightarrow> nat \<Rightarrow> 
    ((nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)) \<Rightarrow> 
    sim_state hrel_des" where 
[sim_blocks]: "FBlock pre m nn f =
  ((\<^bold>\<forall> n::nat \<bullet> (\<guillemotleft>pre\<guillemotright> (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred) \<turnstile>\<^sub>n
    ((\<^bold>\<forall> n::nat \<bullet> 
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>m\<guillemotright>) \<and>
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nn\<guillemotright>) \<and>
      (\<guillemotleft>f\<guillemotright> ($inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u ($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a))) \<and>
      (\<^bold>\<forall> x \<bullet> (\<^bold>\<forall> n::nat \<bullet> ((#\<^sub>u(\<guillemotleft>x\<guillemotright> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m\<guillemotright>) \<Rightarrow> (#\<^sub>u(\<guillemotleft>f\<guillemotright> (\<guillemotleft>x\<guillemotright>)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>nn\<guillemotright>))))
      (* for any inputs, f always produces the same size output. Useful to prove FBlock_seq_comp *)
    ))
  "

lemma pre_true [simp]: "(\<^bold>\<forall> n::nat \<bullet>(\<guillemotleft>\<lambda>x n. True\<guillemotright> (&inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)::sim_state upred) = true"
  by (rel_simp)

subsection {* Number of Inputs and Outputs *}
(* text {* "Dom(x:=x+1)=true" and "Ran(x:=x+1)=(x>0)" *} *)
abbreviation "PrePost(P) \<equiv> pre\<^sub>D(P) \<and> post\<^sub>D(P)"

text {* @{term "SimBlock"} is a condition stating that a design is a Simulink block if it is feasible,
and has $m$ inputs and $n$ outputs. *}
definition SimBlock :: "nat \<Rightarrow> nat \<Rightarrow> sim_state hrel_des \<Rightarrow> bool"
  where [sim_blocks]:
"SimBlock m n P = ((PrePost(P) \<noteq> false) \<and> (* This is stronger than just excluding abort and miracle, and also not the same as H4 feasibility *)
  ((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>m\<guillemotright>) \<sqsubseteq> Dom(PrePost(P))) \<and> 
  ((\<^bold>\<forall> na \<bullet> #\<^sub>u(&inouts(\<guillemotleft>na\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>n\<guillemotright>) \<sqsubseteq> Ran(PrePost(P)))(* \<and>
  (P is \<^bold>N)*))"

axiomatization
  inps :: "sim_state hrel_des \<Rightarrow> nat" and
  outps :: "sim_state hrel_des \<Rightarrow> nat" 
where
  inps_outps: "(SimBlock m n P) \<longrightarrow> (inps P = m) \<and> (outps P = n)"

subsection {* Operators *}
subsubsection {* Id *}

definition f_Id:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_Id x n = [hd(x n)]"

text {* Id block: one input and one output, and the output is always equal to the input *}
definition Id :: "sim_state hrel_des" where
[f_sim_blocks]: "Id = FBlock (\<lambda>x n. True) 1 1 (f_Id)"

subsubsection {* Parallel Composition *}
definition mergeB ::
   "((sim_state des, sim_state des, sim_state des) mrg, 
    sim_state des) urel"  ("B\<^sub>M")  where
[sim_blocks]: "mergeB = (($ok\<acute> =\<^sub>u ($0-ok \<and> $1-ok)) \<and> (
  (\<^bold>\<forall> n::nat \<bullet> (($\<^bold>v\<^sub>D:inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u (\<guillemotleft>append\<guillemotright> ($0-\<^bold>v\<^sub>D:inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a ($1-\<^bold>v\<^sub>D:inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a))
            (*\<and> (#\<^sub>u($\<^bold>v\<^sub>D:inouts\<^sub>< (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u 2)*))))"

text {* @{term "takem"}: a block that just takes the first @{text "nr2"} inputs and 
ignores the remaining inputs. *}
definition takem :: "nat \<Rightarrow> nat \<Rightarrow> sim_state hrel_des" where
[sim_blocks]: "takem nr1 nr2 = ((\<guillemotleft>nr2\<guillemotright> \<le>\<^sub>u \<guillemotleft>nr1\<guillemotright>) \<turnstile>\<^sub>n
    (\<^bold>\<forall> n::nat \<bullet> 
      (uconj ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr1\<guillemotright>) 
      (uconj ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr2\<guillemotright>)
             (true \<triangleleft> (\<guillemotleft>nr2\<guillemotright> =\<^sub>u 0) \<triangleright> (\<guillemotleft>take\<guillemotright> (\<guillemotleft>nr2\<guillemotright>)\<^sub>a ($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a =\<^sub>u ($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)))
    ))))"

text {* @{term "dropm"}: a block that just drops the first @{text "nr2"} inputs and outputs the 
remaining inputs. *}
definition dropm :: "nat \<Rightarrow> nat \<Rightarrow> sim_state hrel_des" where
[sim_blocks]: "dropm nr1 nr2 = ((\<guillemotleft>nr2\<guillemotright> \<le>\<^sub>u \<guillemotleft>nr1\<guillemotright>) \<turnstile>\<^sub>n
    (\<^bold>\<forall> n::nat \<bullet> 
      (uconj ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr1\<guillemotright>) 
      (uconj ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr2\<guillemotright>)
             (true \<triangleleft> (\<guillemotleft>nr2\<guillemotright> =\<^sub>u 0) \<triangleright> (\<guillemotleft>drop\<guillemotright> (\<guillemotleft>nr1-nr2\<guillemotright>)\<^sub>a ($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a =\<^sub>u ($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)))
    ))))"

text {* We use the similar parallel-by-merge in UTP to implement parallel composition. *}
definition sim_parallel :: "
  sim_state hrel_des \<Rightarrow>
  sim_state hrel_des \<Rightarrow>
  sim_state hrel_des" (infixl "\<parallel>\<^sub>B" 60)
where [sim_blocks]: "P \<parallel>\<^sub>B Q = 
  (((takem (inps P + inps Q) (inps P)) ;; P) 
   \<parallel>\<^bsub>mergeB\<^esub> 
   ((dropm (inps P + inps Q) (inps Q)) ;; Q))"

subsubsection {* Sequential Composition *}
text {* It is the same as the sequential composition for designs. *}

subsubsection {* Feedback *}
(* Feedback may cause algebraic loop and how could we characterise it by a healthy condition?
*)
(* An example:
fd (Idm 2) (1,1) = {... \<exists>x. x = x} 
*)
(* text {* @{text "f_PreFD"} has several parameters: a signal, feedback input signal index, input signals, 
and step number. *} *)
definition f_PreFD :: "(nat \<Rightarrow> real) (* input signal: introduced by exists *)
  \<Rightarrow> nat (* the input index number that is fed back from output.  *)
  \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat
  \<Rightarrow> real list" where
[f_blocks]: "f_PreFD x idx_fd inouts0 n = 
    (take idx_fd (inouts0 n)) @ (x n) # (drop idx_fd (inouts0 n))"

(* text {* @{text "f_PostFD"} has several parameters: feedback output signal index, input signals, and 
step number. *} *)
definition f_PostFD :: "
  nat (* the input index number that is fed back from output.  *)
  \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat
  \<Rightarrow> real list" where
[f_blocks]: "f_PostFD idx_fd inouts0 n = 
    (take idx_fd (inouts0 n)) @ (drop (idx_fd+1) (inouts0 n))"

(*
definition PreFD :: "(nat \<Rightarrow> real) (* input signal: introduced by exists *)
  \<Rightarrow> nat (* m *)
  \<Rightarrow> nat (* the input index number that is fed back from output.  *)
  \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "PreFD x nr_of_inputs idx_fd = (true \<turnstile>\<^sub>r
    (\<^bold>\<forall> n::nat \<bullet> (
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr_of_inputs-1\<guillemotright>) \<and> 
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr_of_inputs\<guillemotright>) \<and> 
      (\<^bold>\<forall>na \<bullet> (((\<guillemotleft>na\<guillemotright> <\<^sub>u \<guillemotleft>idx_fd\<guillemotright>) \<Rightarrow> 
          (\<guillemotleft>nth\<guillemotright> ($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a (\<guillemotleft>na\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a (\<guillemotleft>na\<guillemotright>)\<^sub>a)) \<and>
              ((\<guillemotleft>na\<guillemotright> =\<^sub>u \<guillemotleft>idx_fd\<guillemotright>) \<Rightarrow> 
          (\<guillemotleft>nth\<guillemotright> ($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a (\<guillemotleft>na\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>x n\<guillemotright>)) \<and>
              ((\<guillemotleft>na\<guillemotright> >\<^sub>u \<guillemotleft>idx_fd\<guillemotright> \<and> \<guillemotleft>na\<guillemotright> \<le>\<^sub>u \<guillemotleft>nr_of_inputs-1\<guillemotright>) \<Rightarrow> 
          (\<guillemotleft>nth\<guillemotright> ($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a (\<guillemotleft>na\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a (\<guillemotleft>na-1\<guillemotright>)\<^sub>a)))
      \<triangleleft> \<guillemotleft>idx_fd\<guillemotright> \<le>\<^sub>u \<guillemotleft>nr_of_inputs-1\<guillemotright> \<triangleright> 
      false)
    )))"
*)
definition PreFD :: 
  "(nat \<Rightarrow> real) (* input signal: introduced by exists *)
  \<Rightarrow> nat (* m *)
  \<Rightarrow> nat (* the input index number that is fed back from output.  *)
  \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "PreFD x nr_of_inputs idx_fd = (true \<turnstile>\<^sub>n
    (\<^bold>\<forall> n::nat \<bullet> (
      ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr_of_inputs-1\<guillemotright>) \<and> 
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr_of_inputs\<guillemotright>) \<and> 
      ($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>f_PreFD x idx_fd\<guillemotright> ($inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a))
     )))"

(*
definition PostFD :: "(nat \<Rightarrow> real) (* input signal: introduced by exists *)
  \<Rightarrow> nat (* m *)
  \<Rightarrow> nat (* the input index number that is fed back from output.  *)
  \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "PostFD x nr_of_inputs idx_fd = (true \<turnstile>\<^sub>n
        (\<^bold>\<forall> n::nat \<bullet> (
          ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr_of_inputs\<guillemotright>) \<and> 
          ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr_of_inputs-1\<guillemotright>) \<and> 
          (\<^bold>\<forall>na \<bullet> (((\<guillemotleft>na\<guillemotright> <\<^sub>u \<guillemotleft>idx_fd\<guillemotright>) \<Rightarrow> 
            (\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a (\<guillemotleft>na\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>nth\<guillemotright> ($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a (\<guillemotleft>na\<guillemotright>)\<^sub>a)) \<and>
                ((\<guillemotleft>na\<guillemotright> =\<^sub>u \<guillemotleft>idx_fd\<guillemotright>) \<Rightarrow> 
            (\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a (\<guillemotleft>na\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>x n\<guillemotright>)) \<and>
                ((\<guillemotleft>na\<guillemotright> >\<^sub>u \<guillemotleft>idx_fd\<guillemotright> \<and> \<guillemotleft>na\<guillemotright> \<le>\<^sub>u \<guillemotleft>nr_of_inputs-1\<guillemotright>) \<Rightarrow> 
            (\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a (\<guillemotleft>na\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>nth\<guillemotright> ($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a (\<guillemotleft>na-1\<guillemotright>)\<^sub>a)))
          \<triangleleft> \<guillemotleft>idx_fd\<guillemotright> \<le>\<^sub>u \<guillemotleft>nr_of_inputs-1\<guillemotright> \<triangleright> 
          false)
    )))"
*)
definition PostFD :: "(nat \<Rightarrow> real) (* input signal: introduced by exists *)
  \<Rightarrow> nat (* m *)
  \<Rightarrow> nat (* the input index number that is fed back from output.  *)
  \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "PostFD x nr_of_inputs idx_fd = 
    (true \<turnstile>\<^sub>n
        (\<^bold>\<forall> n::nat \<bullet> (
          ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr_of_inputs\<guillemotright>) \<and> 
          ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr_of_inputs-1\<guillemotright>) \<and> 
           ($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>f_PostFD idx_fd\<guillemotright> ($inouts)\<^sub>a (\<guillemotleft>n\<guillemotright>)\<^sub>a)) \<and>
           ((\<guillemotleft>nth\<guillemotright> ($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)\<^sub>a (\<guillemotleft>idx_fd\<guillemotright>)\<^sub>a =\<^sub>u \<guillemotleft>x n\<guillemotright>))
    )))"

text {* The feedback operator @{text "sim_feedback"} is defined via existential quantification. *}
(* The index of pair starts from 0. *)
fun sim_feedback :: "sim_state hrel_des 
  \<Rightarrow> (nat * nat) 
  \<Rightarrow> sim_state hrel_des" (infixl "f\<^sub>D" 60)
where
"P f\<^sub>D (i1,o1) = (\<^bold>\<exists> (x) \<bullet> (PreFD x (inps P) i1 ;; P ;; PostFD x  (outps P) o1))"

(*
definition PreFD' :: "(nat \<Rightarrow> real) (* input signal: introduced by exists *)
  \<Rightarrow> nat (* m *)
  \<Rightarrow> nat (* the input index number that is fed back from output.  *)
  \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "PreFD' x nr idx_fd = FBlock (\<lambda>x n. True) (nr-1) (nr) (f_PreFD x idx_fd)"

definition PostFD' :: "(nat \<Rightarrow> real) (* input signal: introduced by exists *)
  \<Rightarrow> nat (* m *)
  \<Rightarrow> nat (* the input index number that is fed back from output.  *)
  \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "PostFD' x nr idx_fd = 
    FBlock (\<lambda>xx n. (xx n)!idx_fd = x n) (nr) (nr-1) (f_PostFD idx_fd)"

(* The index of pair starts from 0. This definition differs from the above one.
sim_feedback: if it's not solvable, then its post-condition is false, finally miracle.
sim_feedback': if it's not solvable, then its pre-condition is false, finally abort.
*)
fun sim_feedback' :: "sim_state hrel_des 
  \<Rightarrow> (nat * nat) 
  \<Rightarrow> sim_state hrel_des" (infixl "f1\<^sub>D" 60)
where
"P f1\<^sub>D (i1,o1) = (\<^bold>\<exists> (x) \<bullet> (PreFD' x (inps P) i1 ;; P ;; PostFD' x (outps P) o1))"
*)
text {* @{text "Solvable"} checks if the supplied function for feedback is solvable according to 
the feedback signal from the output $o1$ to the input $i1$. A function is solvable if its feedback is 
feasible. Feedback may lead to algebraic loops but this condition states that algebraic loops are 
solvable.
*}
definition Solvable:: "nat (* the input index for feedback *)
    \<Rightarrow> nat (* the output index for feedback *) 
    \<Rightarrow> nat (* how many input signals *)
    \<Rightarrow> nat (* how many output signals *)
    \<Rightarrow> ((nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> real list) (* function *)
    \<Rightarrow> bool" where
"Solvable i1 o1 m nn f = ((i1 < m \<and> o1 < nn) \<and>
  (\<forall>inouts\<^sub>0. (\<forall>x. length(inouts\<^sub>0 x) = (m-1)) (* For any  (m-1) inputs *)
    \<longrightarrow> 
    (\<exists>xx. (* there exists a signal xx that is the i1th input and the o1th output *)
      (\<forall>n. (xx n = (* the o1th output *)
            (f (\<lambda>n1. f_PreFD xx i1 inouts\<^sub>0 n1
                (* ((take i1 (inouts\<^sub>0 n1))@(xx n1)#(drop i1 (inouts\<^sub>0 n1))) *)
                (* assemble of inputs to make xx as i1th *)
               ) n)!o1
           )
      ))))"

text {* @{text "Solvable_unique"}: the feedback is solvable and has a unique solution. *}
definition Solvable_unique:: "nat (* the input index for feedback *)
    \<Rightarrow> nat (* the output index for feedback *) 
    \<Rightarrow> nat (* how many input signals *)
    \<Rightarrow> nat (* how many output signals *)
    \<Rightarrow> ((nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> real list) (* function *)
    \<Rightarrow> bool" where
"Solvable_unique i1 o1 m nn f = ((i1 < m \<and> o1 < nn) \<and>
  (\<forall>inouts\<^sub>0. (\<forall>x. length(inouts\<^sub>0 x) = (m-1)) (* For any  (m-1) inputs *)
    \<longrightarrow> 
    (\<exists>! (xx::nat \<Rightarrow> real). (* there only exists a signal xx that is the i1th input and the o1th output *)
      (\<forall>n. (xx n = (* the o1th output *) (f (\<lambda>n1. f_PreFD xx i1 inouts\<^sub>0 n1) n)!o1)
      )
    )
  )
)"

text {* @{text "Solution"} returns the solution for a feedback block. Here the solution means the signal 
that could satisfy the feedback constraint (the related input is equal to the output) *}
definition Solution:: "nat (* the input index for feedback *)
    \<Rightarrow> nat (* the output index for feedback *) 
    \<Rightarrow> nat (* how many input signals *)
    \<Rightarrow> nat (* how many output signals *)
    \<Rightarrow> ((nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> real list) (* function *)
    \<Rightarrow> (nat \<Rightarrow> real list)
    \<Rightarrow> (nat \<Rightarrow> real)" where
"Solution i1 o1 m nn f inouts\<^sub>0 = 
  (SOME (xx::nat \<Rightarrow> real).
    ((*(\<forall>x. length(inouts\<^sub>0 x) = (m-1)) (* For any  (m-1) inputs *)
    \<longrightarrow> *)
    (\<forall>n. (xx n = 
          (f (\<lambda>n1. f_PreFD xx i1 inouts\<^sub>0 n1
              (* ((take i1 (inouts\<^sub>0 n1))@[xx n1]@(drop i1 (inouts\<^sub>0 n1)))*)
             ) n)!o1
         )
    )))"

text {* @{text "is_Solution"} checks if the supplied solution for a feedback block is a real solution. 
 *}
definition is_Solution:: "nat (* the input index for feedback *)
    \<Rightarrow> nat (* the output index for feedback *) 
    \<Rightarrow> nat (* how many input signals *)
    \<Rightarrow> nat (* how many output signals *)
    \<Rightarrow> ((nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> real list) (* function *)
    \<Rightarrow> ((nat \<Rightarrow> real list) \<Rightarrow> (nat \<Rightarrow> real))
    \<Rightarrow> bool" where
"is_Solution i1 o1 m nn f xx = (
  (\<forall>inouts\<^sub>0. (\<forall>x. length(inouts\<^sub>0 x) = (m-1))
    \<longrightarrow> (\<forall>n. (xx inouts\<^sub>0 n = (f (\<lambda>n1. f_PreFD (xx inouts\<^sub>0) i1 inouts\<^sub>0 n1) n)!o1))))"

subsubsection {* Split *}
definition f_Split2:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_Split2 x n = [hd(x n), hd(x n)]"

definition Split2 :: "sim_state hrel_des" where
[f_sim_blocks]: "Split2 = FBlock (\<lambda>x n. True) 1 2 (f_Split2)"

subsection {* Blocks *}

subsubsection {* Source *}
paragraph {* Constant *}

text {* Constant Block: no inputs and only one output.*}
definition f_Const:: "real \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_Const x0 x n = [x0]"

definition Const :: "real \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "Const c0 = FBlock (\<lambda>x n. True) 0 1 (f_Const c0)"

subsubsection {* Unit Delay *}
text {* Unit Delay block: one parameter (initial output), one input and one output.
  And the output is equal to previous input if it is not the initial output; otherwise
  it is equal to the initial output.
 *}
definition f_UnitDelay:: "real \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_UnitDelay x0 x n = [if n = 0 then x0 else hd(x (n-1))]"

definition UnitDelay :: "real \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "UnitDelay x0 = FBlock (\<lambda>x n. True) 1 1 (f_UnitDelay x0)"

subsubsection {* Discrete-Time Integrator *}
text {* The Discrete-Time Integrator block: performs discrete-time integration or accumulation of 
signal. Integration (T=Ts) or Accumulation (T=1) methods: forward Euler, backward Euler, and 
trapezoidal methods.
*}

text {* @{text "DT_int_fw"}: integration by Forward Euler *}
fun sum_by_fw_euler :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> real"  where
"sum_by_fw_euler 0 x0 K T x = x0" |
"sum_by_fw_euler (Suc m) x0 K T x = 
  (sum_by_fw_euler m x0 K T x) + (K * T * (hd(x m)))"

definition f_DT_int_fw :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_DT_int_fw x0 K T x n = [sum_by_fw_euler n x0 K T x]"

definition DT_int_fw :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 
  sim_state hrel_des" where
[f_sim_blocks]: "DT_int_fw x0 K T = FBlock (\<lambda>x n. True) 1 1 (f_DT_int_fw x0 K T)"

text {* @{text "DT_int_bw"}: integration by Backward Euler (Initial condition setting is set to State) *}
fun sum_by_bw_euler :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> real"  where
"sum_by_bw_euler 0 x0 K T x = x0 + (K * T * (hd(x 0)))" |
"sum_by_bw_euler (Suc m) x0 K T x = 
  (sum_by_bw_euler m x0 K T x) + (K * T * (hd(x m)))"

definition f_DT_int_bw :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_DT_int_bw x0 K T x n = [sum_by_bw_euler n x0 K T x]"

definition DT_int_bw :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "DT_int_bw x0 K T = FBlock (\<lambda>x n. True) 1 1 (f_DT_int_bw x0 K T)"

text {* @{text "DT_int_trape"}: integration by Trapezoidal (Initial condition setting is set to State).
*}
fun sum_by_trape where
"sum_by_trape 0 x0 K T x = x0 + (K * (T div 2) * (hd(x 0)))" |
"sum_by_trape (Suc m) x0 K T x = 
  (sum_by_trape m x0 K T x) + 
  (K * (T div 2) * (hd(x m))) + 
  (K * (T div 2) * (hd(x (Suc m))))"

definition f_DT_int_trape :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_DT_int_trape x0 K T x n = [sum_by_trape n x0 K T x]"

definition DT_int_trape :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 
  sim_state hrel_des" where
[f_sim_blocks]: "DT_int_trape x0 K T =  FBlock (\<lambda>x n. True) 1 1 (f_DT_int_trape x0 K T)"

subsubsection {* Sum *}
text {* The Sum block performs addition or subtraction on its inputs.
*}

text {* @{term "sum_by_sign"}: Summation or subtraction of a list according to their corresponding 
signs. It requires the length of inputs are equal to that of signs (true for +) 
*}
fun sum_by_sign where 
"sum_by_sign [] _ = 0" |
"sum_by_sign (x#xs) (s#ss) = (if s then (sum_by_sign xs ss + x) else (sum_by_sign xs ss - x))"

definition f_SumSub:: "bool list \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_SumSub signs x n = [sum_by_sign (x n) signs]"

text {* @{text "SumSub"}: summation or subtraction according to supplied signs. *}
definition SumSub :: "nat \<Rightarrow> bool list \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "SumSub nr signs = FBlock (\<lambda>x n. True) nr 1 (f_SumSub signs)"

text {* @{text "Sum2"} is a special case of @{text "SumSub"} and it adds up two inputs *}
definition f_Sum2:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_Sum2 x n = [hd(x n) + hd(tl(x n))]"

definition Sum2 :: "sim_state hrel_des" where
[f_sim_blocks]: "Sum2 = FBlock (\<lambda>x n. True) 2 1 (f_Sum2)"

text {* @{text "SumSub2"} is a special case of @{text "SumSub"} and it is equal to subtract 
the second input from the first input. *}
definition f_SumSub2 :: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_SumSub2 x n = [hd(x n) - hd(tl(x n))]"

definition SumSub2 :: "sim_state hrel_des" where
[f_sim_blocks]: "SumSub2 = FBlock (\<lambda>x n. True) 2 1 (f_SumSub2)"

text {* @{text "SubSum2"} is a special case of @{text "SumSub"} and it is equal to subtract 
the first input from the second input. *}
definition f_SubSum2 :: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_SubSum2 x n = [- hd(x n) + hd(tl(x n))]"

definition SubSum2 :: "sim_state hrel_des" where
[f_sim_blocks]: "SubSum2 = FBlock (\<lambda>x n. True) 2 1 (f_SubSum2)"

subsubsection {* Product *}
text {* The Product block performs multiplication and division.
*}

text {* @{term "not_divide_by_zero"} is a predicate in assumption. For signs, true denotes * and false for /.
*}
fun not_divide_by_zero where 
"not_divide_by_zero [] _ = True" |
"not_divide_by_zero (x#xs) (s#ss) = 
  (HOL.conj (not_divide_by_zero xs ss) (if s then True else (x \<noteq> 0)))"

text {* @{term "product_by_sign"}: multiplies or divides by signs. *}
fun product_by_sign where
"product_by_sign [] _ = 1" |
"product_by_sign (x#xs) (s#ss) = 
  (if s then (product_by_sign xs ss * x) else (product_by_sign xs ss / x))"

definition f_ProdDiv :: "bool list \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_ProdDiv signs x n = [product_by_sign (x n) signs]"

definition f_no_div_by_zero :: "bool list \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> bool" where
[f_blocks]: "f_no_div_by_zero signs x n = not_divide_by_zero (x n) signs"

text {* @{text "ProdDiv"} has additional precondition that assumes all values of the divisor inputs 
are not equal to zero. *}
definition ProdDiv :: "nat \<Rightarrow> bool list \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "ProdDiv nr signs = FBlock (\<lambda>x n. (f_no_div_by_zero signs x n)) nr 1 (f_ProdDiv signs)"

text {* @{text "Mul2"} is a special case of @{text "ProdDiv"} and it multiplies two inputs. *}
definition f_Mul2:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_Mul2 x n = [hd(x n) * hd(tl(x n))]"

definition Mul2 :: "sim_state hrel_des" where
[f_sim_blocks]: "Mul2 = FBlock (\<lambda>x n. True) 2 1 (f_Mul2)"

text {* @{text "Div2"} is a special case of @{text "ProdDiv"} and the first input is divided by the 
second input. *}
definition f_Div2:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_Div2 x n = [hd(x n) / hd(tl(x n))]"

definition Div2 :: "sim_state hrel_des" where
[f_sim_blocks]: "Div2 = FBlock (\<lambda>x n. (hd(tl(x n)) \<noteq> 0)) 2 1 (f_Div2)"

subsubsection {* Gain *}
definition f_Gain:: "real \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_Gain k x n = [k * hd(x n)]"

definition Gain :: "real \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "Gain k = FBlock (\<lambda>x n. True) 1 1 (f_Gain k)"

subsubsection {* Saturation *}
definition f_Limit:: "real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_Limit ymin ymax x n = 
                [if ymin > hd(x n) then ymin else 
                    (if ymax < hd(x n) then ymax else hd(x n))]"

definition Limit :: "real \<Rightarrow> real \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "Limit ymin ymax = FBlock (\<lambda>x n. True) 1 1 (f_Limit ymin ymax)"

subsubsection {* MinMax *}
text {* @{term "MinList"}: return the minimum number from a list of numbers.
*}
fun MinList where
"MinList [] minx = minx" |
"MinList (x#xs) minx = 
     (if x < minx 
      then MinList xs x 
      else MinList xs minx)"

text {* The input list must not be empty. *}
abbreviation "MinLst \<equiv> (\<lambda> lst . MinList lst (hd(lst)))"

text {* @{term "MaxList"}: return the maximum number from a list of numbers.
*}
fun MaxList where
"MaxList [] maxx = maxx" |
"MaxList (x#xs) maxx = 
     (if x > maxx 
      then MaxList xs x 
      else MaxList xs maxx)"

text {* The input list must not be empty. *}
abbreviation "MaxLst \<equiv> (\<lambda> lst . MaxList lst (hd(lst)))"

text {* @{text "MinN"} returns the minimum value in the inputs. *}
definition f_MinN:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_MinN x n = [MinLst (x n)]"

definition MinN :: "nat \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "MinN nr = FBlock (\<lambda>x n. True) nr 1 (f_MinN)"

definition f_Min2:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_Min2 x n = [min (hd(x n)) (hd(tl(x n)))]"

definition Min2 :: "sim_state hrel_des" where
[f_sim_blocks]: "Min2 = FBlock (\<lambda>x n. True) 2 1 (f_Min2)"

text {* @{text "MaxN"} returns the maximum value in the inputs. *}
definition f_MaxN:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_MaxN x n = [MaxLst (x n)]"

definition MaxN :: "nat \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "MaxN nr = FBlock (\<lambda>x n. True) nr 1 (f_MaxN)"

definition f_Max2:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_Max2 x n = [max (hd(x n)) (hd(tl(x n)))]"

definition Max2 :: "sim_state hrel_des" where
[f_sim_blocks]: "Max2 = FBlock (\<lambda>x n. True) 2 1 (f_Max2)"

subsubsection {* Rounding *}
text {* The Rounding Function block applies a rounding function to the input signal to produce the 
output signal.
*}

text {* @{text "RoundFloor"} rounds inputs using the floor function. *}
definition f_RoundFloor:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_RoundFloor x n = [real_of_int \<lfloor>(hd(x n))\<rfloor>]"

definition RoundFloor :: "sim_state hrel_des" where
[f_sim_blocks]: "RoundFloor = FBlock (\<lambda>x n. True) 1 1 (f_RoundFloor)"

text {* @{text "RoundCeil"} rounds inputs using the ceil function. *}
definition f_RoundCeil:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_RoundCeil x n = [real_of_int \<lceil>(hd(x n))\<rceil>]"

definition RoundCeil :: "sim_state hrel_des" where
[f_sim_blocks]: "RoundCeil = FBlock (\<lambda>x n. True) 1 1 (f_RoundCeil)"

(* subsubsection {* Combinatorial Logic *}
text {* Combinatorial Logic: implements truth table. It has one input (vector) and one output (vector).
Its data type is described below.
\begin{itemize}
  \item 1. Boolean logic signals option: ;
    \begin{itemize}
      \item If the option is enabled, the block accepts Boolean or double. Truth table should be Boolean
  type (0 or 1 only), or double (if a non-Boolean value exists in the table). If both the input and the 
  table are Boolean, then the output is Boolean. If the input is Boolean and the table is double, then 
  the output is double. If the input is double, then the output is double no matter what type the table is;
      \item If the option is disabled, the block only accepts Boolean. The output type is the same as the 
  table type.
    \end{itemize} 
  \item 2. The relationship between the number of inputs and the number of rows is:
      number of rows = 2 ^ (number of inputs)
\end{itemize} 
*}

abbreviation "power2n nr \<equiv> 2 ^ nr"

subparagraph {* @{term "row_index"} *}
text {* @{term "row_index"}: row index = 1 + u(m)*2^0 + u(m-1)*2^1 + ... + u(1)*2^(m-1). *}

fun row_index :: "real list (* input list: zero as 0 and non-zero as 1 *)
      \<Rightarrow> nat (* number of inputs *)
      \<Rightarrow> nat (* index *)
      \<Rightarrow> nat" 
  where
"row_index [] nr _ = 1" |
"row_index (x#xs) nr index = 
  (row_index xs nr (index+1)) + 
  ((if x = 0 then 0 else 1) * (power2n (nr - index)))"

lemma "row_index [0, 1] 2 1 = 2"
apply (auto)
done

lemma "row_index [1, 1] 2 1 = 4"
apply (auto)
done

text {* @{term "CombLogic"}: both input and output are vector. Assume
\begin{itemize}
  \item the input is Boolean, and the table is Boolean too, then the output is Boolean (data type: real)
\end{itemize}
*}
(* This is not going to be supported in this version because we use real for each input and output.
But the input of CombLogic is a vector (list). 
*) (*
definition CombLogic where
[f_sim_blocks]: "CombLogic nr table = Pat11 
  ((((#\<^sub>u(\<guillemotleft>table\<guillemotright>)) =\<^sub>u \<guillemotleft>power2n\<guillemotright> (\<guillemotleft>nr\<guillemotright>)\<^sub>a) (* the number of rows is equal to 2 ^ number of inputs *)
  \<and> (\<^bold>\<forall> n::nat \<bullet> (#\<^sub>u(head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr\<guillemotright>)))) 
  (* *)
  (\<lambda> n. (\<guillemotleft>nth\<guillemotright> (\<guillemotleft>table\<guillemotright>)\<^sub>a ((\<guillemotleft>row_index\<guillemotright> (head\<^sub>u($inouts (n)\<^sub>a))\<^sub>a (\<guillemotleft>nr\<guillemotright>)\<^sub>a (1)\<^sub>a) - 1)\<^sub>a))"
*)
*)

subsubsection {* Logic Operators *}
text {* The Logical Operator block performs the specified logical operation on its inputs. 
\begin{itemize}
  \item It supports seven operators: AND, OR, NAND, NOR, XOR, NXOR, NOT;
  \item An input value is TRUE (1) if it is nonzero and FALSE (0) if it is zero;
  \item An output value is 1 if TRUE and 0 if FALSE;
\end{itemize}
*}

paragraph {* AND *}
fun LAnd :: "real list \<Rightarrow> bool" where
"LAnd [] = True" |
"LAnd (x#xs) = (if x = 0 then False else (LAnd xs))"

definition f_LopAND:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_LopAND x n = [if LAnd (x n) then 1 else 0]"

definition LopAND :: "nat \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "LopAND m = FBlock (\<lambda>x n. True) m 1 (f_LopAND)"

paragraph {* OR *}
fun LOr :: "real list \<Rightarrow> bool" where
"LOr [] = False" |
"LOr (x#xs) = (if x \<noteq> 0 then True else (LOr xs))"

definition f_LopOR:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_LopOR x n = [if LOr (x n) then 1 else 0]"

definition LopOR :: "nat \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "LopOR m = FBlock (\<lambda>x n. True) m 1 (f_LopOR)"

paragraph {* NAND *}
fun LNand :: "real list \<Rightarrow> bool" where
"LNand [] = False" |
"LNand (x#xs) = (if x = 0 then True else (LNand xs))"

definition f_LopNAND:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_LopNAND x n = [if LNand (x n) then 1 else 0]"

definition LopNAND :: "nat \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "LopNAND m = FBlock (\<lambda>x n. True) m 1 (f_LopNAND)"

paragraph {* NOR *}
fun LNor :: "real list \<Rightarrow> bool" where
"LNor [] = True" |
"LNor (x#xs) = (if x \<noteq> 0 then False else (LNand xs))"

definition f_LopNOR:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_LopNOR x n = [if LNor (x n) then 1 else 0]"

definition LopNOR :: "nat \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "LopNOR m = FBlock (\<lambda>x n. True) m 1 (f_LopNOR)"

paragraph {* XOR *}
fun LXor :: "real list \<Rightarrow> nat \<Rightarrow> bool" where
"LXor [] t = (if t mod 2 = 0 then False else True)" |
"LXor (x#xs) t = (if x \<noteq> 0 then (LXor xs (t+1)) else (LXor xs t))"

lemma "LXor [0, 1, 1] 0 = False"
by auto

lemma "LXor [0, 1, 1, 1] 0 = True"
by auto

definition f_LopXOR:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_LopXOR x n = [if LXor (x n) 0 then 1 else 0]"

definition LopXOR :: "nat \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "LopXOR m = FBlock (\<lambda>x n. True) m 1 (f_LopXOR)"

paragraph {* NXOR *}
fun LNxor :: "real list \<Rightarrow> nat \<Rightarrow> bool" where
"LNxor [] t = (if t mod 2 = 0 then True else False)" |
"LNxor (x#xs) t = (if x \<noteq> 0 then (LNxor xs (t+1)) else (LNxor xs t))"

lemma "LNxor [0, 1, 1] 0 = True"
by auto

lemma "LNxor [0, 1, 1, 1] 0 = False"
by auto

definition f_LopNXOR:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_LopNXOR x n = [if LNxor (x n) 0 then 1 else 0]"

definition LopNXOR :: "nat \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "LopNXOR m = FBlock (\<lambda>x n. True) m 1 (f_LopNXOR)"

paragraph {* NOT *}
definition f_LopNOT:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_LopNOT x n = [if hd(x n) = 0 then 1 else 0]"

definition LopNOT :: "sim_state hrel_des" where
[f_sim_blocks]: "LopNOT = FBlock (\<lambda>x n. True) 1 1 (f_LopNOT)"

subsubsection {* Relational Operator *}
text {* The Relational Operator block performs specified relational operation on inputs. 
\begin{itemize}
  \item It supports six operators for two-input mode: ==, ~=, <, <=, >, >=;
  \item An output value is 1 if TRUE and 0 if FALSE;
\end{itemize}
*}

paragraph {* Equal == *}
definition f_RopEQ:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_RopEQ x n = [if hd(x n) = hd(tl(x n)) then 1 else 0]"

definition RopEQ :: "sim_state hrel_des" where
[f_sim_blocks]: "RopEQ = FBlock (\<lambda>x n. True) 2 1 (f_RopEQ)"

paragraph {* Notequal ~= *}
definition f_RopNEQ:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_RopNEQ x n = [if hd(x n) = hd(tl(x n)) then 0 else 1]"

definition RopNEQ :: "sim_state hrel_des" where
[f_sim_blocks]: "RopNEQ = FBlock (\<lambda>x n. True) 2 1 (f_RopNEQ)"

paragraph {* Less Than < *}
definition f_RopLT:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_RopLT x n = [if hd(x n) < hd(tl(x n)) then 1 else 0]"

definition RopLT :: "sim_state hrel_des" where
[f_sim_blocks]: "RopLT = FBlock (\<lambda>x n. True) 2 1 (f_RopLT)"

paragraph {* Less Than or Equal to <= *}
definition f_RopLE:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_RopLE x n = [if hd(x n) \<le> hd(tl(x n)) then 1 else 0]"

definition RopLE :: "sim_state hrel_des" where
[f_sim_blocks]: "RopLE = FBlock (\<lambda>x n. True) 2 1 (f_RopLE)"

paragraph {* Greater Than > *}
definition f_RopGT:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_RopGT x n = [if hd(x n) > hd(tl(x n)) then 1 else 0]"

definition RopGT :: "sim_state hrel_des" where
[f_sim_blocks]: "RopGT = FBlock (\<lambda>x n. True) 2 1 (f_RopGT)"

paragraph {* Greater Than or Equal to >= *}
definition f_RopGE:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_RopGE x n = [if hd(x n) \<ge> hd(tl(x n)) then 1 else 0]"

definition RopGE :: "sim_state hrel_des" where
[f_sim_blocks]: "RopGE = FBlock (\<lambda>x n. True) 2 1 (f_RopGE)"

(* subsubsection {* Mux *}
text {* The Mux block: combines its inputs into a single vector output. 
\begin{itemize}
  \item Inputs could be scalar or vector;
  \item The output is a vector;
\end{itemize}
*}
(*
definition Mux :: "nat \<Rightarrow> (('a, 'b) sim_state_scheme des, ('a list, 'c) sim_state_scheme des) rel_des" where
[f_sim_blocks]: "Mux nr = (true \<turnstile>\<^sub>n
   (\<^bold>\<forall> n::nat \<bullet> 
      (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr\<guillemotright>) \<and> ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and>
      ((head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u ($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)))
   ))
)"
*)
subsubsection {* Demux *}
text {* The Demux block: extract and output elements of vector signal. 
\begin{itemize}
  \item The input is vector;
  \item Provide the size of the input is n, and the number of outputs is p;
    \begin{itemize}
      \item if p == n, then outputs are p scalar signals;
      \item if p > n, then error;
      \item ... (see reference manual of Simulink).
    \end{itemize}
\end{itemize}
*}

text {* @{term "Demux"}: assume p == n *}
(*
definition Demux :: "nat \<Rightarrow> (('a list, 'b) sim_state_scheme des, ('a, 'c) sim_state_scheme des) rel_des" where
[f_sim_blocks]: "Demux nr = (
    (\<^bold>\<forall> n::nat \<bullet> ((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr\<guillemotright>))
   \<turnstile>\<^sub>n
    (\<^bold>\<forall> n::nat \<bullet> 
      (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr\<guillemotright>) \<and>
      ((($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)))
    ))
)"
*)
*)

subsubsection {* Switch *}
text {* The Switch block switches the output between the first input and the third input based on 
the value of the second input. 
\begin{itemize}
  \item The first and the third inputs are data inputs;
  \item The second is the control input.
  \item Criteria for passing first input: $u2 \geq Threshold$, $u2 > Threshold$, or $u2 ~= 0$;
\end{itemize}
*}

text {* @{term "Switch1"}: criteria is $u2 \geq Threshold$ *}
definition f_Switch1:: "real \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_Switch1 th x n = [if (x n)!1 \<ge> th then (x n)!0 else (x n)!2]"

definition Switch1 :: "real \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "Switch1 th = FBlock (\<lambda>x n. True) 3 1 (f_Switch1 th)"

text {* @{term "Switch2"}: criteria is $u2 > Threshold$ *}
definition f_Switch2:: "real \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_Switch2 th x n = [if (x n)!1 > th then (x n)!0 else (x n)!2]"

definition Switch2 :: "real \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "Switch2 th = FBlock (\<lambda>x n. True) 3 1 (f_Switch2 th)"

text {* @{term "Switch3"}: criteria is $u2 ~= 0$ *}
definition f_Switch3:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_Switch3 x n = [if (x n)!1 = 0 then (x n)!2 else (x n)!0]"

definition Switch3 :: "sim_state hrel_des" where
[f_sim_blocks]: "Switch3 = FBlock (\<lambda>x n. True) 3 1 (f_Switch3)"

(* subsubsection {* Merge *}
text {* The Merge block: combines its inputs into a single output line whose value at any time is 
equal to the most recently computed output of its driving blocks. Use Merge blocks only to interleave 
input signals that update at different times into a combined signal in which the interleaved values 
retain their separate identities and times.
*}
*)
(*
definition Merge :: "nat \<Rightarrow> (('a, 'b) sim_state_scheme des, ('a list, 'c) sim_state_scheme des) rel_des" where
[f_sim_blocks]: "Merge nr = (true \<turnstile>\<^sub>n
   (\<^bold>\<forall> n::nat \<bullet> 
      (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u \<guillemotleft>nr\<guillemotright>) \<and> ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and>
      ((head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u ($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)))
   ))
)"
*)

(*subsubsection {* Subsystem *}
text {* A Subsystem *}

subsubsection {* Action Subsystem *}
text {* Action subsystems are subsystems that execute in response to a conditional output from an 
If block or a Switch Case block.
\begin{itemize}
  \item All blocks in an If Action Subsystem must run at the same rate as the driving If block;
\end{itemize}
*}

subsubsection {* Enabled Subsystem *}

subsubsection {* Triggered Subsystem *}

subsubsection {* Enabled and Triggered Subsystem *}
*)
subsubsection {* Data Type Conversion *}
text {*  Data Type Conversion: converts an input signal to the specified data type. 
*}

text {* Integer round number towards zero *}
definition RoundZero :: "real \<Rightarrow> int" where
"RoundZero x = (if x \<ge> (0::real) then \<lfloor>x\<rfloor> else \<lceil>x\<rceil>)"

lemma "RoundZero 1.1 = 1"
apply (simp add: RoundZero_def)
done

lemma "RoundZero (-1.1) = -1"
apply (simp add: RoundZero_def)
done

text {* @{term "int8"}: convert int to int8. *}
definition int8 :: "int \<Rightarrow> int" where
"int8 x = ((x+128) mod 256) - 128"

text {* @{term "int16"}: convert int to int16. *}
definition int16 :: "int \<Rightarrow> int" where
"int16 x = ((x+32768) mod 65536) - 32768"

text {* @{term "int32"}: convert int to int32. *}
definition int32 :: "int \<Rightarrow> int" where
"int32 x = ((x+2147483648) mod 4294967296) - 2147483648"

lemma int32_eq:
  assumes "x \<ge> 0 \<and> x < 2147483648"
  shows "int32 x = x"
  apply (simp add: int32_def)
  using assms by (smt int_mod_eq)

lemma "int8 (-1) = -1"
by (simp add: int8_def)

lemma "int8 (-128) = -128"
by (simp add: int8_def)

lemma "int8 (-129) = 127"
by (simp add: int8_def)

lemma "int8 (129) = -127"
by (simp add: int8_def)

lemma "int8 (-378) = -122"
by (simp add: int8_def)

lemma "int8 (378) = 122"
by (simp add: int8_def)

text {* @{term "uint8"}: convert int to uint8  *}
definition uint8 :: "int \<Rightarrow> int" where
"uint8 x = x mod 256"

lemma "uint8 (-1) = 255"
by (simp add: uint8_def)

text {* @{term "uint16"}: convert int to uint16  *}
definition uint16 :: "int \<Rightarrow> int" where
"uint16 x = x mod 65536"

text {* @{term "uint32"}: convert int to uint32  *}
definition uint32 :: "int \<Rightarrow> int" where
"uint32 x = x mod 4294967296"

lemma "(uint32 4294967296) = 0"
  by (simp add: uint32_def)

lemma "(uint32 4294967295) = 4294967295"
  by (simp add: uint32_def)

lemma "(uint32 (-1)) = 4294967295"
  by (simp add: uint32_def)

lemma "(uint32 (-4294967298)) = 4294967294"
  by (simp add: uint32_def)

(*
datatype DataTypeMode = ModDouble | ModSingle | ModInt8 | ModUInt8
  | ModInt16 | ModUInt16 | ModInt32 | ModUInt32 | ModBoolean (*| ModFixdt | Enum *)

datatype IntRoundMode = IntModFloor (* *)
  | IntModCeiling (*
  | IntModConvergent (* *)
  | IntModNear (* *)
  | IntModRound 
  | IntModSimp *)
  | IntModZero
*)
text {* @{term "DataTypeConvUint32Zero"}: convert to uint32 and round number towards zero. *}
(* 1. Round a real towards 0 and becomes a int
   2. int \<Rightarrow> 32 Word
   3. 32 Word \<Rightarrow> unsigned int
   4. unsigned int \<Rightarrow> real
*)
definition f_DTConvUint32Zero:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_DTConvUint32Zero x n = [real_of_int (uint32 (RoundZero(hd (x n))))]"

definition DataTypeConvUint32Zero :: "sim_state hrel_des" where
[f_sim_blocks]: "DataTypeConvUint32Zero = FBlock (\<lambda>x n. True) 1 1 (f_DTConvUint32Zero)"

text {* @{term "DataTypeConvInt32Zero"}: convert to int32 and round number towards zero. *}
definition f_DTConvInt32Zero:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_DTConvInt32Zero x n = [real_of_int (int32 (RoundZero(hd (x n))))]"

definition DataTypeConvInt32Zero :: "sim_state hrel_des" where
[f_sim_blocks]: "DataTypeConvInt32Zero = FBlock (\<lambda>x n. True) 1 1 (f_DTConvInt32Zero)"

text {* @{term "DataTypeConvUint32Floor"}: convert to uint32 and round number using floor. *}
definition f_DTConvUint32Floor:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_DTConvUint32Floor x n = [real_of_int (uint32 (\<lfloor>(hd (x n))\<rfloor>))]"

definition DataTypeConvUint32Floor :: "sim_state hrel_des" where
[f_sim_blocks]: "DataTypeConvUint32Floor = FBlock (\<lambda>x n. True) 1 1 (f_DTConvUint32Floor)"

text {* @{term "DataTypeConvInt32Floor"}: convert to int32 and round number using floor. *}
definition f_DTConvInt32Floor:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_DTConvInt32Floor x n = [real_of_int (int32 (\<lfloor>(hd (x n))\<rfloor>))]"

definition DataTypeConvInt32Floor :: "sim_state hrel_des" where
[f_sim_blocks]: "DataTypeConvInt32Floor = FBlock (\<lambda>x n. True) 1 1 (f_DTConvInt32Floor)"

text {* @{term "DataTypeConvUint32Ceil"}: convert to uint32 and round number using ceil. *}
definition f_DTConvUint32Ceil:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_DTConvUint32Ceil x n = [real_of_int (uint32 (\<lceil>(hd (x n))\<rceil>))]"

definition DataTypeConvUint32Ceil :: "sim_state hrel_des" where
[f_sim_blocks]: "DataTypeConvUint32Ceil = FBlock (\<lambda>x n. True) 1 1 (f_DTConvUint32Ceil)"

text {* @{term "DataTypeConvInt32Ceil"}: convert to int32 and round number using ceil. *}
definition f_DTConvInt32Ceil:: "(nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_DTConvInt32Ceil x n = [real_of_int (int32 (\<lceil>(hd (x n))\<rceil>))]"

definition DataTypeConvInt32Ceil :: "sim_state hrel_des" where
[f_sim_blocks]: "DataTypeConvInt32Ceil = FBlock (\<lambda>x n. True) 1 1 (f_DTConvInt32Ceil)"

subsubsection {* Initial Condition (IC) *}
text {* The IC block sets the initial condition of the signal at its input port. The block does this 
by outputting the specified initial condition when you start the simulation, regardless of the 
actual value of the input signal. Thereafter, the block outputs the actual value of the input signal.
*}

definition f_IC:: "real \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_IC x0 x n = [if n = 0 then x0 else hd(x n)]"

definition IC :: "real \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "IC x0 = FBlock (\<lambda>x n. True) 1 1 (f_IC x0)"

subsubsection {* Router Block *}
text {* A new introduced block to route signals: the same number of inputs and outputs but in
different orders. *}

(* The 2nd parameter (routes) is a map from inputs to outputs. Here the index of list denotes
the same index in the output and the number of the index means the corresponding inputs. 
For example, [2, 0, 1] means the map [(2,0), (0,1), (1, 2)] *)
fun assembleOutput:: "real list \<Rightarrow> nat list \<Rightarrow> real list" where
"assembleOutput ins [] = []" |
"assembleOutput ins (x#xs) = (ins!x)#(assembleOutput ins (xs))"

definition f_Router:: "nat list \<Rightarrow> (nat \<Rightarrow> real list) \<Rightarrow> nat \<Rightarrow> (real list)" where
[f_blocks]: "f_Router routes x n = assembleOutput (x n) routes"

lemma "f_Router [2,0,1] (\<lambda>na. [11, 22, 33]) n = [33, 11, 22]"
  by (simp add: f_blocks)

definition Router :: "nat \<Rightarrow> nat list \<Rightarrow> sim_state hrel_des" where
[f_sim_blocks]: "Router nn routes = FBlock (\<lambda>x n. True) nn nn (f_Router routes)"

(*
subsubsection {* Lookup Table (1-D) *}
text {* Lookup Table (N-D): Approximate N-dimensional function. the block maps inputs to an output value by looking up or interpolating 
a table of values you define with block parameters.
\begin{itemize}
  \item n from 1 to 30;
  \item Breakpoints: indices; such as [1;3;5;10] - for input value match
  \item Table data: output values for associated indices; such as [0.05;0.1;0.5;1.0] - associated 
    values for 1,3,5,10 respectively.
  \item Interpolation methods: flat (constant), linear, and cubic-spline;
  \item Extrapolation methods: flat (constant), linear, and cubic-spline;
  \item Index search method: Evenly spaced points, Linear search, or Binary search;
\end{itemize}

This block produces the output by the procedures below.
\begin{itemize}
  \item 1), if the input value matches indices in the breakpoint data sets, it outputs the associated
value in table data sets. For example, if the input value is 3, then it outputs 0.1 for the setting 
above.
  \item 2), if the input value doesn't match indices in the breakpoint data sets but is within range,
then interpolates appropriate table values, using the Interpolation method you select.
  \item 3), if the input value doesn't match indices in the breakpoint data sets and is out of range,
then extrapolates the output value, using the Extrapolation method you select.
\end{itemize}
*}

text {* This implements a 1-D lookup table using linear interpolation and extrapolation methods. Here
if the input is out of range, the linear extrapolation method will use the first pair breakpoints (if
the input is less than the first breakpoint) or the last pair breakpoints (if the input is larger than
the last breakpoint). *}

(* last_but_one [..., y, x] return y *)
abbreviation "last_but_one \<equiv> \<lambda>x. hd(tl(rev x))" 

text {* Search indices from breakpoints. Here assume the size of list is more than 2, and elements are 
sorted by ascending order.*}
fun GetIndices :: "real 
  \<Rightarrow> real list 
  \<Rightarrow> nat (* the index number of current item (x) in the list *)
  \<Rightarrow> nat * nat" where
"GetIndices input [x] ia = 
  (if input = x then (ia, ia) else (if input < x then (ia-1, ia) else undefined))" |
"GetIndices input (x#xs) ia = 
  (if input = x then (ia, ia) 
   else (if input < x then (if ia = 0 then undefined else (ia-1, ia)) 
         else (GetIndices input xs (ia+1)))
  )
"
lemma "GetIndices 0.1 [0, 0.05, 0.2, 0.4] 0 = (1,2)"
apply (auto)
done

lemma "GetIndices 0.1 [0, 0.2, 0.4] 0 = (0,1)"
apply (auto)
done

lemma "GetIndices 0.1 [0.2, 0.3, 0.4] 0 = undefined"
apply (auto)
done

lemma "GetIndices 0.5 [0.2, 0.3, 0.4] 0 = undefined"
apply (auto)
done

lemma "GetIndices 0.1 [0, 0.1, 0.2, 0.4] 0 = (1,1)"
apply (auto)
done

lemma "GetIndices 0.4 [0, 0.1, 0.2, 0.4] 0 = (3,3)"
apply (auto)
done

text {* Using linear methods for interpolation and extrapolation to get approximation value *}
definition ApproximateLinear :: "real \<Rightarrow> real list \<Rightarrow> real list \<Rightarrow> real" where
"ApproximateLinear input breakpoints table = 
  (
    if (input < hd(breakpoints)) (* extrapolation *)
    then (* ((v1 - v0)/(idx1 - idx0))*(input-idx0) + v0*)
      (((nth table 1 - hd table) / (nth breakpoints 1 - hd breakpoints)) * (input - hd breakpoints) + hd table)
    else
      (if (input > last(breakpoints)) (* extrapolation *)
      then  (* ((v1 - v0)/(idx1 - idx0))*(input-idx0) + v0*)
        (((last_but_one table - last table) / (last_but_one breakpoints - last breakpoints)) * 
          (input - last breakpoints) + last table)
      else (* interpolation *) (* ((v1 - v0)/(idx1 - idx0))*(input-idx0) + v0*)
        (let (ia,ib) = GetIndices input breakpoints 0
         in (if ia=ib then (nth table ia) 
             else ((((nth table ib) - (nth table ia)) / ((nth breakpoints ib) - (nth breakpoints ia))) *
                    (input - (nth breakpoints ia)) + ((nth table ia)))
        ))
      )
  )"

lemma "GetIndices 0.2 [0,0.05,0.2,0.4,1] 0 = (2,2)"
by auto

lemma "ApproximateLinear 0.2 [0,0.05,0.2,0.4,1] [0, 0.12, 0.23, 0.34, 1] = 0.23"
apply (simp add: ApproximateLinear_def)
done

lemma "ApproximateLinear 0.1 [0,0.05,0.2,0.4,1] [0, 0.12, 0.23, 0.34, 1] = 
  (((0.23-0.12)/(0.2-0.05))*(0.1-0.05)+0.12)"
apply (simp add: ApproximateLinear_def)
done

(* The dimension and size of breakpoints and table data should be the same. 
Both sizes must be at least 2*)
definition LookUp1D :: "real list \<Rightarrow> (* breakpoints *)
  real list \<Rightarrow> (* Table data *)
  sim_state hrel_des" where
[f_sim_blocks]: "LookUp1D breakpoints table = (true \<turnstile>\<^sub>n
   (\<^bold>\<forall> n::nat \<bullet> 
      (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> 
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and>
      (head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u \<guillemotleft>ApproximateLinear\<guillemotright> (head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a))\<^sub>a (\<guillemotleft>breakpoints\<guillemotright>)\<^sub>a (\<guillemotleft>table\<guillemotright>)\<^sub>a)
   ))
)"

subsubsection {* Discrete Transfer Function *}
paragraph {* Auxiliary Functions *}
(* Polynomial Addition: (a1*x^1+ a2*x^2+...+ an*x^n) + (b1*x^1+ b2*x^2+...+ bm*x^m) as
PolyAdd [a1 a2 ... an] [b1 b2 ... bm]*)
fun PolyAdd :: "real list \<Rightarrow> real list \<Rightarrow> real list" where
"PolyAdd [] x = x" |
"PolyAdd x [] = x" |
"PolyAdd (x#xs) (y#ys) = (x+y)#(PolyAdd xs ys)"

lemma "(PolyAdd [3] [1,2]) = [4,2]"
by auto

lemma "(PolyAdd [1,2,3] [5,6]) = [6,8,3]"
by auto

(* Polynomial Multiplication: (a1*x^1+ a2*x^2+...+ an*x^n) * (b1*x^1+ b2*x^2+...+ bm*x^m) as
PolyMul [a1 a2 ... an] [b1 b2 ... bm]*)
fun PolyMul :: "real list \<Rightarrow> real list \<Rightarrow> real list" where
"PolyMul [] x = []" |
"PolyMul (x#xs) (ys) = PolyAdd (map (\<lambda>y.(x*y)) ys) (0#(PolyMul xs ys))"

lemma "PolyMul [1, 2] [2] = [2, 4]"
by auto

lemma "PolyMul [2, 1] [1, 1] = [2, 3, 1]"
by auto

lemma "PolyMul [1, 2, 3] [4, 5, 6] = [4, 13, 28, 27, 18]"
by auto

(* zeros or poles to polynomial. Such as zeros=[1,2], (z-1)*(z-2) = PolyMul [-1,1] [-2,1] = [2,-3,1] *)
fun ZerosPoles2Poly::"real list \<Rightarrow> real list" where
"ZerosPoles2Poly [] = [1]" | 
"ZerosPoles2Poly (x#xs) = PolyMul [-x,1] (ZerosPoles2Poly xs)" 

lemma "ZerosPoles2Poly [] = [1]"
  by simp
lemma "ZerosPoles2Poly [0.99] = [-0.99,1]" by auto
lemma "ZerosPoles2Poly [1,2] = [2, -3, 1]" by auto

(* a polynomial list into expressions *)
fun Poly2Exp :: "real list \<Rightarrow> ((nat \<Rightarrow> real list, 'd) uexpr) \<Rightarrow> nat \<Rightarrow> (real, 'd) uexpr"  where
"Poly2Exp [] expr m = 0" |
"Poly2Exp (x#xs) expr m = (\<guillemotleft>x\<guillemotright> * (head\<^sub>u(expr (\<guillemotleft>m\<guillemotright>)\<^sub>a)) + Poly2Exp xs expr (m+1))" 

lemma "Poly2Exp [] ($inouts) n = 0" by simp
lemma Poly2Exp_one:
  fixes n :: "nat"
  shows "Poly2Exp [1] ($inouts) n = (1*(head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)))"
  apply (auto)
  by rel_auto

lemma Poly2Exp_two:
  fixes n :: "nat"
  shows "Poly2Exp [1,2] ($inouts) n = (1*(head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a))) + (2*(head\<^sub>u($inouts (\<guillemotleft>n+1\<guillemotright>)\<^sub>a)))"
  apply (auto)
  by rel_auto

paragraph {* Discrete Transfer Function *}
text {* H(z)=(N(z)/D(z))=(n0*z^m+n1*z^(m-1)...+nm)/(d0*z^n+d1*z^(n-1)...+dn). 
Initial state denotes initial filter state. What does it mean? 
*}
(* But how to cope with sample rate Ts ?? *)
(* Experiment of initial state: 
Parameters:
  Numerator: [0.01], Denominator: [1 -0.99], Initial states: 0.2, sample time: 0.1s
  Input: a step with step time: 1s, initial value: 0, Final value: 1, sample time: 0.1s

Output: y[0] = 0.002, y[0.1] = 0.00198, y[0.2] = 0.0019602, ..., y[1.0] = 

Analsis: 
  Difference equation: y[n+1] = 0.99y[n] + 0.01x[n]
  y[0*0.1] = 0.01*0.2 = 0.002 (here initial state may be for x[n]?)
  y[1*0.1] = 0.99*y[0] + 0.01*x[0] = 0.99*0.002 + 0.01*0 (step) = 0.00198
  y[2*0.1] = 0.99*y[1] + 0.01*x[1] = 0.99*0.00198 + 0.01*0 (step) = 0.0019602
*)
definition DiscreteTransFn :: "real list \<Rightarrow> (* numerator: given in ascending order [nm, ..., n0] *)
  real list \<Rightarrow> (* denominator: given in ascending order [dm, ..., d0] *)
  real \<Rightarrow> (* initial state: assume it is always 0 *)
  sim_state hrel_des" where
[f_sim_blocks]: "DiscreteTransFn numerator denominator ic = (true \<turnstile>\<^sub>n
   (\<^bold>\<forall> n::nat \<bullet> 
      (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> 
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and>
      (head\<^sub>u($inouts\<acute> (\<guillemotleft>0\<guillemotright>)\<^sub>a) =\<^sub>u 0) \<and>
      (Poly2Exp (numerator) ($inouts) n) =\<^sub>u 
        (Poly2Exp (denominator) ($inouts\<acute>) n)
   ))
)"

subsubsection {* Zero-Pole Discrete Transfer Function *}
text {* Model system defined by zeros and poles of discrete transfer function. 
\begin{itemize}
  \item H(z)=(k((z-z0)(z-z1)...)/((z-p0)(z-p1)...))
  \item transform to H(z)=(k((1-z0/z)(1-z1/z)...)/((1-p0/z)(1-p1/z)...))
  \item then apply inverse z-transform to (Y(z)/X(z)=H(z)) to get the difference equation.
\end{itemize}
Alternative, we can expand H(z) to polynomial (H(z)=k(z^n+a*z^(n-1)+...+an)/(z^m+b*z^(m-1)+...+bm)),
then the difference equation would be 
  

if zeros=[-1] and poles=[0.9], then @{text "H(z)=Y(z)/X(z)=(z+1)/(z-0.9)=(1+z\<^sup>-\<^sup>1)/(1-0.9z\<^sup>-\<^sup>1)"}, so
@{text "X(z)+z\<^sup>-\<^sup>1 X(z) = Y(z)-0.9z\<^sup>-\<^sup>1 Y(z)"}.
Since for z-transform 
  @{text "z-trans(x[n-n0]) = z\<^sup>-\<^sup>n\<^sup>0X(z)"}
  @{text "z-trans(x[n]) = X(z)"}
, apply inverse z-transform to the equation, we get its difference equation
  @{text "inv-z-trans(X(z)+z\<^sup>-\<^sup>1 X(z) = Y(z)-0.9z\<^sup>-\<^sup>1 Y(z)) = (x[n]+x[n-1] = y[n]-0.9y[n-1])"}.

Alternatively, @{text "H(z)=Y(z)/X(z)=(z+1)/(z-0.9)"}, then 
  (zX(z)+X(z) = zY(z)-0.9 Y(z)), apply inverse z-transform, we get the difference equation below,
  x[n+1]+x[n] = y[n+1]-0.9y[n].

If k=0.01, zeros=[] and poles=[0.99], then H(z)=0.01/(z-0.99). So y[n+1]-0.99y[n]=0.01x[n], then
  y[n+1]=0.99y[n]+0.01x[n].
*}

(* But how to cope with sample rate Ts ?? *)
(* Initial condition: see help for transfer function (assume zero initial condition)
A transfer function describes the relationship between input and output in Laplace (frequency) domain. 
Specifically, it is defined as the Laplace transform of the response (output) of a system with 
zero initial conditions to an impulse input.
*)
definition ZeroPoleDiscreteFn :: "real list \<Rightarrow> (* zeros *)
  real list \<Rightarrow> (* poles *)
  real \<Rightarrow> (* gain *)
  sim_state hrel_des" where
[f_sim_blocks]: "ZeroPoleDiscreteFn zeros poles gain = (true \<turnstile>\<^sub>n
   (\<^bold>\<forall> n::nat \<bullet> 
      (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> 
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and>
       (head\<^sub>u($inouts\<acute> (\<guillemotleft>0\<guillemotright>)\<^sub>a) =\<^sub>u 0) \<and>
       ((Poly2Exp (PolyMul [gain] (ZerosPoles2Poly zeros)) ($inouts) n) =\<^sub>u 
         (Poly2Exp ((ZerosPoles2Poly poles)) ($inouts\<acute>) n))
   ))
)"

(* If k=0.01, zeros=[] and poles=[0.99], then y[n+1]=0.99y[n]+0.01x[n]. *)
lemma "ZeroPoleDiscreteFn [] [0.99] 0.01 = (true \<turnstile>\<^sub>n
   (\<^bold>\<forall> n::nat \<bullet> 
      (((#\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and> 
      ((#\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a)) =\<^sub>u 1) \<and>
       (head\<^sub>u($inouts\<acute> (\<guillemotleft>0\<guillemotright>)\<^sub>a) =\<^sub>u 0) \<and>
       (0.01*head\<^sub>u($inouts (\<guillemotleft>n\<guillemotright>)\<^sub>a) =\<^sub>u head\<^sub>u($inouts\<acute> (\<guillemotleft>n+1\<guillemotright>)\<^sub>a) - 0.99*head\<^sub>u($inouts\<acute> (\<guillemotleft>n\<guillemotright>)\<^sub>a))
   ))
)"
apply (simp add: f_sim_blocks)
apply (rel_auto)
done

lemma DisTrFn2ZerosPolesEqual:
  "DiscreteTransFn [0.01] [-0.99,1] 0 = ZeroPoleDiscreteFn [] [0.99] 0.01"
apply (simp add: f_sim_blocks)
done
*)
end
