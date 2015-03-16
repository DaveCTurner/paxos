theory Paxos
  imports Main
begin

locale propNoL =
  fixes lt :: "'pid \<Rightarrow> 'pid \<Rightarrow> bool" (infixl "\<prec>" 50)
  fixes le :: "'pid \<Rightarrow> 'pid \<Rightarrow> bool" (infixl "\<preceq>" 50)
  assumes le_lt_eq [simp]: "\<And>p q. p \<preceq> q = (p \<prec> q \<or> p = q)"
  assumes wf: "wf {(p,q). p \<prec> q}"
  assumes trans: "trans {(p,q). p \<prec> q}"
  assumes total: "\<And>p q. p \<prec> q \<or> p = q \<or> q \<prec> p"

lemma (in propNoL) propNo_acyclic: "acyclic {(p,q). p \<prec> q}"
  using local.wf by (intro wf_acyclic)

lemma (in propNoL) propNo_cases:
  assumes lt: "p1 \<prec> p2  \<Longrightarrow> P"
  and eq: "p1 = p2  \<Longrightarrow> P"
  and gt: "p2 \<prec> p1  \<Longrightarrow> P"
  shows P
  using assms total by auto

lemma (in propNoL) propNo_leE [elim]:
  assumes le1: "p1 \<preceq> p2"
  and lt: "p1 \<prec> p2 \<Longrightarrow> P"
  and eq: "p1 = p2 \<Longrightarrow> P"
  shows P
  using assms local.le_lt_eq by auto

lemma (in propNoL) propNo_irreflexive [simp]:
  shows "\<not> p \<prec> p"
  by (metis local.wf mem_Collect_eq old.prod.case wf_irrefl)

lemma (in propNoL) propNo_trans_lt_lt [trans]:
  "p1 \<prec> p2 \<Longrightarrow> p2 \<prec> p3 \<Longrightarrow> p1 \<prec> p3"
  using trans by (elim transE, auto)

lemma (in propNoL) propNo_lt_not_ge_E [elim]:
  assumes lt: "p1 \<prec> p2"
  and not_gt: "\<lbrakk> p1 \<noteq> p2; \<not>(p2 \<prec> p1) \<rbrakk>  \<Longrightarrow> P"
  shows P
  by (metis lt not_gt propNo_irreflexive propNo_trans_lt_lt)

lemma (in propNoL) propNo_trans_lt_le [trans]:
  "p1 \<prec> p2 \<Longrightarrow> p2 \<preceq> p3 \<Longrightarrow> p1 \<prec> p3"
  by (metis le_lt_eq propNo_trans_lt_lt)

lemma (in propNoL) propNo_trans_le_lt [trans]:
  "p1 \<preceq> p2 \<Longrightarrow> p2 \<prec> p3 \<Longrightarrow> p1 \<prec> p3"
  by (metis le_lt_eq propNo_trans_lt_lt)

lemma (in propNoL) propNo_trans_le_le [trans]:
  assumes p12: "p1 \<preceq> p2" and p23: "p2 \<preceq> p3"
  shows "p1 \<preceq> p3"
  by (metis le_lt_eq p12 p23 propNo_trans_lt_le)


fun weight :: "('acc \<Rightarrow> nat) \<Rightarrow> 'acc set \<Rightarrow> nat"
  where "weight f S = setsum f { a \<in> S. f a \<noteq> 0 }"

fun isWeightedMajority :: "('acc \<Rightarrow> nat) \<Rightarrow> 'acc set \<Rightarrow> bool"
  where "isWeightedMajority f S = (finite { a. f a \<noteq> 0 } \<and> finite S \<and> weight f UNIV < 2 * weight f S)"

lemma
  assumes S1: "isWeightedMajority f1 S1"
  assumes S2: "isWeightedMajority f2 S2"
  assumes d1: "d \<le> 1"
  assumes fa0: "f2 a0 = f1 a0 + d"
  assumes f: "\<And>a. a \<noteq> a0 \<Longrightarrow> f1 a = f2 a"
  shows weighted_majority_intersects: "S1 \<inter> S2 \<noteq> ({} :: 'acc set)"
proof (intro notI)
  assume inter: "S1 \<inter> S2 = {}"

  {
    have halves_gt: "\<And>a b c::nat. c < 2 * a \<Longrightarrow> c \<le> 2 * b \<Longrightarrow> c < a + b" by linarith
  
    presume "weight f1 UNIV \<le> 2 * weight f1 S2"
    with S1 have "weight f1 UNIV < weight f1 S1 + weight f1 S2"
      by (intro halves_gt, simp_all)
  
    also presume "weight f1 S1 + weight f1 S2 = weight f1 (S1 \<union> S2)"
  
    also have "weight f1 (S1 \<union> S2) \<le> weight f1 UNIV"
    using S1 by (unfold weight.simps, intro setsum_mono3, auto)
  
    finally show False by simp
  
  next
    show "weight f1 S1 + weight f1 S2 = weight f1 (S1 \<union> S2)"
    proof -
      have "weight f1 (S1 \<union> S2) = setsum f1 {a \<in> S1 \<union> S2. f1 a \<noteq> 0}" by simp
      also have "... = setsum f1 ({ a \<in> S1. f1 a \<noteq> 0 } \<union> { a \<in> S2. f1 a \<noteq> 0 })"
        by (rule cong [where f = "setsum f1"], auto)
      also have "... = weight f1 S1 + weight f1 S2" 
      proof (unfold weight.simps, intro setsum.union_disjoint)
        from S1 show "finite {a \<in> S1. f1 a \<noteq> 0}" and "finite {a \<in> S2. f1 a \<noteq> 0}" by auto
        from inter show "{a \<in> S1. f1 a \<noteq> 0} \<inter> {a \<in> S2. f1 a \<noteq> 0} = {}" by auto
      qed
      finally show "weight f1 S1 + weight f1 S2 = weight f1 (S1 \<union> S2)" ..
    qed

  next
    presume "weight f1 UNIV + d = weight f2 UNIV"
    also from S2 have "... < 2 * weight f2 S2" by simp
    
    also presume "weight f2 S2 \<le> weight f1 S2 + d"
    hence "2 * weight f2 S2 \<le> 2 * (weight f1 S2 + d)" by simp

    finally show "weight f1 UNIV \<le> 2 * weight f1 S2" using d1 by simp

  next
    have p: "\<And>S. a0 \<notin> S \<Longrightarrow> weight f2 S = weight f1 S"
    proof -
      fix S
      assume a0S: "a0 \<notin> S"
      with f have eq: "\<And>a. a \<in> S \<Longrightarrow> f1 a = f2 a" by metis

      also from eq a0S have "setsum f2 { a \<in> S. f2 a \<noteq> 0 } = setsum f1 { a \<in> S. f1 a \<noteq> 0 }"
        by (intro setsum.cong sym [OF f] equalityI subsetI CollectI conjI, auto)

      thus "?thesis S" by simp
    qed

    have q: "\<And>S. weight f2 S = weight f1 S + (if a0 \<in> S then d else 0)"
    proof (cases "d = 0")
      case True
      have "f2 = f1"
      proof (intro ext)
        fix a from f fa0 True show "f2 a = f1 a" by (cases "a = a0", auto)
      qed
      with True show "\<And>S. ?thesis S" by simp
    next
      case False
      with d1 have d: "d = 1" by simp

      fix S
  
      show "?thesis S"
      proof (cases "a0 \<in> S")
        case False
        with p [OF this] show ?thesis by simp
      next
        case True
        note a0S = this
        from d fa0 have fa01: "f2 a0 = f1 a0 + 1" by simp
  
        have add_cong: "\<And>a b c d :: nat. a = c \<Longrightarrow> b = d \<Longrightarrow> a + b = c + d" by linarith
  
        have "weight f2 S = setsum f2 { a \<in> S. f2 a \<noteq> 0 }" by simp
        also from fa01 True have "... = setsum f2 (insert a0 { a \<in> (S - {a0}). f2 a \<noteq> 0 })"
          by (intro setsum.cong refl, auto)
        also from S2 have "... = f2 a0 + setsum f2 {a \<in> (S - {a0}). f2 a \<noteq> 0}"
          by (intro setsum.insert, simp_all)
        also have "... = f2 a0       + weight f2 (S - {a0})" by simp
        also have "... = (f1 a0 + 1) + weight f1 (S - {a0})"
          by (intro add_cong [OF fa01] p, simp)
        also have "... = (f1 a0 + weight f1 (S - {a0})) + 1" by simp
        also have "... = weight f1 S + (if a0 \<in> S then 1 else 0)"
        proof (intro add_cong)
          from True show "1 = (if a0 \<in> S then 1 else 0)" by simp
  
          show "f1 a0 + weight f1 (S - {a0}) = weight f1 S"
          proof (cases "f1 a0 = 0")
            case True
            have "weight f1 (S - {a0}) = weight f1 S"
              by (unfold weight.simps, metis True member_remove remove_def)
            with True show ?thesis by simp
          next
            case False
            have "f1 a0 + weight f1 (S - {a0}) = f1 a0 + setsum f1 { a \<in> S - {a0}. f1 a \<noteq> 0 }" by simp
            also from S1 have "... = setsum f1 (insert a0 { a \<in> S - {a0}. f1 a \<noteq> 0 })"
              by (intro sym [OF setsum.insert], simp_all)
            also from a0S False have "... = setsum f1 { a \<in> S. f1 a \<noteq> 0 }"
              by (intro setsum.cong refl, auto)
            also have "... = weight f1 S" by simp
            finally show ?thesis .
          qed
        qed
        also from d have "... = weight f1 S + (if a0 \<in> S then d else 0)" by simp
        finally show ?thesis .
      qed
    qed

    thus "weight f1 UNIV + d = weight f2 UNIV"
      by (auto simp del: weight.simps)

    from q show "weight f2 S2 \<le> weight f1 S2 + d"
      by (cases "a0 \<in> S", auto simp del: weight.simps)
  }
qed

locale paxosL = propNoL +

  fixes quorum_proposer :: "'pid \<Rightarrow> 'aid set \<Rightarrow> bool"
  fixes quorum_learner  :: "'pid \<Rightarrow> 'aid set \<Rightarrow> bool"
  fixes promised_free :: "'aid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes promised_prev :: "'aid \<Rightarrow> 'pid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes proposed :: "'pid \<Rightarrow> bool"
  fixes accepted :: "'aid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes chosen :: "'pid \<Rightarrow> bool"
  fixes value_promised :: "'aid \<Rightarrow> 'pid \<Rightarrow> 'value"
  fixes value_proposed :: "'pid \<Rightarrow> 'value"
  fixes value_accepted :: "'aid \<Rightarrow> 'pid \<Rightarrow> 'value"

  assumes quorum_inter: "\<And> SP SL p0 p1.
    \<lbrakk> quorum_proposer p1 SP; quorum_learner p0 SL; chosen p0; proposed p1; p0 \<prec> p1 \<rbrakk>
    \<Longrightarrow> SP \<inter> SL \<noteq> {}"

  assumes quorum_finite: "\<And> SP p. quorum_proposer p SP \<Longrightarrow> finite SP"

  assumes quorum_exists: "\<And>p. EX SP. quorum_proposer p SP"

  assumes quorum_nonempty: "\<And> SL p. quorum_learner p SL \<Longrightarrow> SL \<noteq> {}"

  assumes proposed_quorum:
    "\<And> p . proposed p \<Longrightarrow> EX S. quorum_proposer p S
      \<and> (ALL a:S. promised_free a p \<or> (EX p1. promised_prev a p p1))
      \<and> (ALL a1:S. ALL p1. promised_prev a1 p p1
          \<longrightarrow> value_proposed p = value_promised a1 p
          \<or> (EX a2:S. EX p2. promised_prev a2 p p2 \<and> p1 \<prec> p2))"

  assumes promised_free:
    "\<And> a p0 p1. \<lbrakk> promised_free a p0; accepted a p1 \<rbrakk> \<Longrightarrow> p0 \<preceq> p1"

  assumes promised_prev_accepted:
    "\<And> a p0 p1. promised_prev a p0 p1 \<Longrightarrow> accepted a p1"
  assumes promised_prev_prev:
    "\<And> a p0 p1. promised_prev a p0 p1 \<Longrightarrow> p1 \<prec> p0"
  assumes promised_prev_max:
    "\<And> a p0 p1 p2. \<lbrakk> promised_prev a p0 p1; accepted a p2; p2 \<prec> p0 \<rbrakk>
      \<Longrightarrow> ((p1 = p2 \<and> value_accepted a p1 = value_promised a p0) \<or> p2 \<prec> p1)"

  assumes accepts_proposed:
    "\<And> p a. accepted a p \<Longrightarrow> proposed p"
  assumes accepts_value:
    "\<And> p a. accepted a p \<Longrightarrow> value_accepted a p = value_proposed p"

  assumes chosen_quorum:
    "\<And> p . chosen p \<Longrightarrow> EX S. quorum_learner p S \<and> (ALL a:S. accepted a p)"

lemma (in paxosL) promised_some_none:
  assumes "promised_prev a p0 p1" "promised_free a p0"
  shows P
proof -
  have "promised_prev a p0 p1 \<longrightarrow> \<not> promised_free a p0"
    by (metis promised_free promised_prev_accepted promised_prev_prev propNo_leE propNo_lt_not_ge_E)
  with assms show P by simp
qed

lemma (in paxosL) promised_prev_fun:
  assumes "promised_prev a p0 p1" "promised_prev a p0 p2"
  shows "p1 = p2"
  by (metis assms promised_prev_accepted promised_prev_max promised_prev_prev propNo_lt_not_ge_E)

lemma (in paxosL)
  assumes "quorum_proposer p S"
  shows paxos_max_proposer: "(ALL a0:S. ALL p1. \<not> promised_prev a0 p p1)
 \<or> (EX a1:S. EX p1. promised_prev a1 p p1
         \<and> (ALL a3:S. ALL p3. promised_prev a3 p p3 \<longrightarrow> p3 \<preceq> p1))"
  (is "?P1 S \<or> ?P2 S")
proof -
  from assms quorum_finite
  have "finite S" by simp
  thus ?thesis
  proof (induct S rule: finite_induct)
    case empty thus ?case by simp
  next
    case (insert a S')

    show ?case
    proof (cases "EX p0. promised_prev a p p0")
      case False
      from insert.hyps
      show ?thesis
      proof (elim disjE)
        assume hyp1: "?P1 S'"
        show ?thesis
          by (intro disjI1 ballI allI impI, metis False hyp1 insert_iff)
      next
        assume hyp2: "?P2 S'"
        then obtain a1 p1 where a1S: "a1 \<in> S'" and p: "promised_prev a1 p p1"
          and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S'; promised_prev a3 p p3 \<rbrakk> \<Longrightarrow> p3 \<preceq> p1"
          by auto

        show ?thesis
        proof (intro disjI2 bexI exI conjI ballI allI impI)
          from p show "promised_prev a1 p p1" .
          from a1S show "a1 \<in> insert a S'" by simp
          fix a3 p3
          assume "a3 \<in> insert a S'" and "promised_prev a3 p p3"
          thus "p3 \<preceq> p1" by (metis False insert_iff p1_max)
        qed
      qed
    next
      case True
      then obtain p0 where p0: "promised_prev a p p0" by auto

      from insert.hyps
      have "?P2 (insert a S')"
      proof (elim disjE)
        assume "?P1 S'"
        hence none_proposed: "\<And> a1 p1 P. \<lbrakk> a1 \<in> S'; promised_prev a1 p p1 \<rbrakk> \<Longrightarrow> P" by simp
        show ?thesis
        proof (intro bexI exI conjI impI ballI allI)
          show "a \<in> insert a S'" by simp
          from p0 show "promised_prev a p p0" .
          fix a3 p3
          assume "a3 \<in> insert a S'" and p: "promised_prev a3 p p3"
          thus "p3 \<preceq> p0"
            by (metis insert_iff le_lt_eq none_proposed p0 promised_prev_fun)
        qed
      next
        assume "?P2 S'"
        then obtain a1 p1 where a1S: "a1 \<in> S'" and p: "promised_prev a1 p p1"
          and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S'; promised_prev a3 p p3 \<rbrakk> \<Longrightarrow> p3 \<preceq> p1" by auto
        have le: "p0 \<preceq> p1 \<Longrightarrow> ?thesis"
        proof (intro bexI exI conjI ballI allI impI)
          assume p10: "p0 \<preceq> p1"
          hence p10_cases: "p0 \<prec> p1 \<or> p0 = p1" by simp
          from p show "promised_prev a1 p p1" .
          from a1S show "a1 \<in> insert a S'" by simp
          fix a3 p3
          assume "a3 \<in> insert a S'"
            and p3: "promised_prev a3 p p3"
          hence "a3 = a \<or> a3 \<in> S'" by simp
          from this p10_cases show "p3 \<preceq> p1"
          apply (elim disjE)
          apply (metis p0 p10 p3 promised_prev_fun)
          apply (metis le_lt_eq p0 p3 promised_prev_fun)
          apply (metis p1_max p3)
            by (metis p1_max p3)
        qed

        show ?thesis
        proof (rule propNo_cases)
          assume "p1 = p0" with le show ?thesis by simp
        next
          assume "p0 \<prec> p1" with le show ?thesis by simp
        next
          assume p1p: "p1 \<prec> p0"
          show ?thesis
          proof (intro bexI exI conjI ballI allI impI)
            from p0 show "promised_prev a p p0" .
            show "a \<in> insert a S'" by simp
            fix a3 p3
            assume "a3 \<in> insert a S'"
              and p3: "promised_prev a3 p p3"
            hence "a3 = a \<or> a3 \<in> S'" by simp
            thus "p3 \<preceq> p0"
              apply (elim disjE)
              apply (metis le_lt_eq p0 p3 promised_prev_fun)
              by (metis le_lt_eq p1_max p1p p3 propNo_trans_le_le)
          qed
        qed
      qed

      thus ?thesis by simp
    qed
  qed
qed

lemma (in paxosL) p2c:
  assumes proposed_p0: "proposed p0"
  obtains S where "quorum_proposer p0 S"
    and "(ALL a1 : S. ALL p1. p1 \<prec> p0 \<longrightarrow> \<not> accepted a1 p1)
    \<or> (EX a1 : S. EX p1. accepted a1 p1
        \<and> value_proposed p0 = value_accepted a1 p1
        \<and> p1 \<prec> p0
        \<and> (ALL a2 : S. ALL p2. (accepted a2 p2 \<and> p2 \<prec> p0) \<longrightarrow> p2 \<preceq> p1))"
proof -
  from proposed_quorum [OF proposed_p0]
  obtain S where quorum_S: "quorum_proposer p0 S"
    and S_promised: "\<And> a1. a1 \<in> S \<Longrightarrow> promised_free a1 p0 \<or> (\<exists>p1. promised_prev a1 p0 p1)"
    and S_value: "\<And>a1 p1. \<lbrakk> a1 \<in> S; promised_prev a1 p0 p1 \<rbrakk> \<Longrightarrow> value_proposed p0 = value_promised a1 p0 \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev a2 p0 p2 \<and> p1 \<prec> p2)"
    by auto
  show thesis
  proof (intro that)
    from quorum_S show "quorum_proposer p0 S" .
    show "(ALL a1 : S. ALL p1. p1 \<prec> p0 \<longrightarrow> \<not> accepted a1 p1)
        \<or> (EX a1 : S. EX p1. accepted a1 p1
            \<and> value_proposed p0 = value_accepted a1 p1
            \<and> p1 \<prec> p0
            \<and> (ALL a2 : S. ALL p2. (accepted a2 p2 \<and> p2 \<prec> p0) \<longrightarrow> p2 \<preceq> p1))"
    (is "?ALLFRESH \<or> ?EXISTSMAX")
    proof (cases "ALL a1:S. promised_free a1 p0")
      case True
      show ?thesis
        by (metis True promised_free propNo_irreflexive propNo_trans_lt_le)
    next
      case False
      then obtain a2 where a2S: "a2 \<in> S" and not_None: "\<not> promised_free a2 p0" by auto
      from S_promised a2S not_None obtain p2 where p2: "promised_prev a2 p0 p2" by metis

      from paxos_max_proposer [OF quorum_S]
      obtain a1 p1
        where a1S: "a1 \<in> S"
        and p1: "promised_prev a1 p0 p1"
        and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S; promised_prev a3 p0 p3 \<rbrakk> \<Longrightarrow> p3 \<preceq> p1"
          by (metis a2S p2)

      have lt10: "p1 \<prec> p0" by (metis p1 promised_prev_prev)

      show ?thesis
      proof (intro exI conjI disjI2 bexI ballI allI impI)
        from p1 show acc1: "accepted a1 p1" by (metis promised_prev_accepted)
        from a1S show "a1 \<in> S" .

        from S_value [OF a1S p1]
        show "value_proposed p0 = value_accepted a1 p1"
          by (metis acc1 lt10 p1 p1_max promised_prev_max propNo_irreflexive propNo_trans_lt_le)

        from lt10 show "p1 \<prec> p0" .

        fix a3 p3 assume a3S: "a3 \<in> S" and p3: "accepted a3 p3 \<and> p3 \<prec> p0"

        from a3S S_promised obtain p4 where p4: "promised_prev a3 p0 p4"
          by (metis p3 promised_free propNo_leE propNo_lt_not_ge_E)

        show "p3 \<preceq> p1"
          by (metis a3S le_lt_eq p1_max p3 p4 promised_prev_max propNo_trans_le_le)
      qed
    qed
  qed
qed

lemma (in paxosL) p2b:
  assumes chosen: "chosen p0"
  shows "\<And>p1. \<lbrakk> proposed p1; p0 \<prec> p1 \<rbrakk> \<Longrightarrow> value_proposed p0 = value_proposed p1"
proof -
  from chosen_quorum [OF chosen] obtain SL
    where SC_quorum: "quorum_learner p0 SL"
    and SC_accepts: "\<And>a. \<lbrakk> a \<in> SL \<rbrakk> \<Longrightarrow> accepted a p0" by auto

  fix p1_base
  assume "proposed p1_base" "p0 \<prec> p1_base" thus "?thesis p1_base"
  proof (induct p1_base rule: wf_induct [OF wf])
    fix p1
    assume proposed: "proposed p1" and p01: "p0 \<prec> p1"
    assume "\<forall>p2. (p2, p1) \<in> {(p,q). p \<prec> q} \<longrightarrow> proposed p2 \<longrightarrow> p0 \<prec> p2 \<longrightarrow> value_proposed p0 = value_proposed p2"
      hence
      hyp: "\<And>p2. \<lbrakk> p2 \<prec> p1; proposed p2; p0 \<prec> p2 \<rbrakk> \<Longrightarrow> value_proposed p0 = value_proposed p2" by auto

    from p2c [OF proposed] obtain SP where SP_quorum: "quorum_proposer p1 SP"
      and S_mess: "((\<forall>a1\<in>SP. \<forall>p1a. p1a \<prec> p1 \<longrightarrow> \<not> accepted a1 p1a)
      \<or> (\<exists>a1\<in>SP. \<exists>p1a. accepted a1 p1a \<and> value_proposed p1 = value_accepted a1 p1a \<and> p1a \<prec> p1
          \<and> (\<forall>a2\<in>SP. \<forall>p2. accepted a2 p2 \<and> p2 \<prec> p1 \<longrightarrow> p2 \<preceq> p1a)))"
      (is "?P1 \<or> ?P2") by auto

    from SP_quorum SC_quorum quorum_inter chosen proposed p01
    obtain a where aSP: "a \<in> SP" and aSC: "a \<in> SL"
      by (metis disjoint_iff_not_equal)

    from S_mess
    show "value_proposed p0 = value_proposed p1"
    proof (elim disjE)
      assume "?P1"
      thus ?thesis
        by (metis SC_accepts aSC aSP p01)
    next
      assume "?P2"
      thus ?thesis
        by (metis SC_accepts aSC aSP accepts_proposed accepts_value hyp p01 propNo_leE)
    qed
  qed
qed

lemma (in paxosL)
  assumes "chosen p0" and "accepted a1 p1" and "p0 \<prec> p1"
  shows p2a: "value_proposed p0 = value_proposed p1"
  using assms by (intro p2b accepts_proposed)

lemma (in paxosL)
  assumes chosen0: "chosen p0"
  assumes chosen1: "chosen p1"
  assumes p01: "p0 \<prec> p1"
  shows p2: "value_proposed p0 = value_proposed p1"
proof -
  from chosen_quorum [OF chosen1]
  obtain S where QL: "quorum_learner p1 S" and acc: "\<And>a. a \<in> S \<Longrightarrow> accepted a p1" by auto
  from quorum_nonempty [OF QL] obtain a where aS: "a \<in> S" by auto
  show ?thesis by (metis p2a chosen0 p01 acc aS)
qed

theorem (in paxosL)
  assumes chosen0: "chosen p0"
  assumes chosen1: "chosen p1"
  shows paxos_consistent: "value_proposed p0 = value_proposed p1"
  by (metis assms le_lt_eq p2 propNo_cases)

locale multiPaxosL = propNoL +

  fixes inst_le :: "'iid \<Rightarrow> 'iid \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)

  fixes quorum           :: "nat \<Rightarrow> 'aid set \<Rightarrow> bool"
  fixes topology_version :: "'pid \<Rightarrow> nat"
  fixes instance_topology_version :: "'iid \<Rightarrow> nat"

  (* multi_promised i a p  is effectively promised_free j a p for all j \<ge> i *)
  fixes multi_promised :: "'iid \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> bool"

  fixes promised_free  :: "'iid \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes promised_prev  :: "'iid \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes proposed       :: "'iid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes accepted       :: "'iid \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes chosen         :: "'iid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes value_promised :: "'iid \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> 'value"
  fixes value_proposed :: "'iid \<Rightarrow> 'pid \<Rightarrow> 'value"
  fixes value_accepted :: "'iid \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> 'value"

  assumes topology_version_mono: "\<And>p0 p1. p0 \<preceq> p1 \<Longrightarrow> topology_version p0 \<le> topology_version p1"

  assumes quorum_inter:     "\<And>tv S1 S2. quorum      tv  S1 \<Longrightarrow> quorum tv S2 \<Longrightarrow> S1 \<inter> S2 \<noteq> {}"
  assumes quorum_inter_Suc: "\<And>tv S1 S2. quorum (Suc tv) S1 \<Longrightarrow> quorum tv S2 \<Longrightarrow> S1 \<inter> S2 \<noteq> {}"

  assumes quorum_finite: "\<And>tv S. quorum tv S \<Longrightarrow> finite S"

  assumes quorum_exists: "\<And>tv. EX S. quorum tv S"

  assumes quorum_nonempty: "\<And>tv S. quorum tv S \<Longrightarrow> S \<noteq> {}"

  assumes proposed_quorum:
    "\<And> i p . proposed i p \<Longrightarrow> EX S.
      (quorum (topology_version p) S)
      \<and> (ALL a:S. (promised_free i a p 
        \<or> (\<exists>j. j \<sqsubseteq> i \<and> multi_promised j a p))
        \<or> (EX p1. promised_prev i a p p1))
      \<and> (ALL a1:S. ALL p1. promised_prev i a1 p p1
          \<longrightarrow> value_proposed i p = value_promised i a1 p
          \<or> (EX a2:S. EX p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2))"

  assumes proposed_topology:
    "\<And> i p. proposed i p \<Longrightarrow> topology_version p \<le> instance_topology_version i"

  assumes promised_free:
    "\<And> i a p0 p1. \<lbrakk> promised_free i a p0; accepted i a p1 \<rbrakk> \<Longrightarrow> p0 \<preceq> p1"

  assumes multi_promised:
    "\<And>i j a p0 p1. \<lbrakk> multi_promised i a p0; accepted j a p1; i \<sqsubseteq> j \<rbrakk> \<Longrightarrow> p0 \<preceq> p1"

  assumes promised_prev_accepted:
    "\<And> i a p0 p1. promised_prev i a p0 p1 \<Longrightarrow> accepted i a p1"
  assumes promised_prev_prev:
    "\<And> i a p0 p1. promised_prev i a p0 p1 \<Longrightarrow> p1 \<prec> p0"
  assumes promised_prev_max:
    "\<And> i a p0 p1 p2. \<lbrakk> promised_prev i a p0 p1; accepted i a p2; p2 \<prec> p0 \<rbrakk>
      \<Longrightarrow> ((p1 = p2 \<and> value_accepted i a p1 = value_promised i a p0) \<or> p2 \<prec> p1)"

  assumes accepts_proposed:
    "\<And> i p a. accepted i a p \<Longrightarrow> proposed i p"
  assumes accepts_value:
    "\<And> i p a. accepted i a p \<Longrightarrow> value_accepted i a p = value_proposed i p"

  assumes chosen_quorum:
    "\<And> i p . chosen i p \<Longrightarrow> EX S. quorum (topology_version p) S \<and> (ALL a:S. accepted i a p)"

  assumes chosen_topology:
    "\<And> i p. chosen i p \<Longrightarrow> instance_topology_version i \<le> Suc (topology_version p)"

lemma (in multiPaxosL)
  multi_instances: "\<And>i. paxosL lt le
    (%p S. quorum (topology_version p) S)
    (%p S. quorum (topology_version p) S)
    (%a p. promised_free i a p \<or> (EX j. j \<sqsubseteq> i \<and> multi_promised j a p))
    (promised_prev i) (proposed i) (accepted i) (chosen i)
    (value_promised i) (value_proposed i) (value_accepted i)"
proof (unfold paxosL_def paxosL_axioms_def, intro allI impI conjI)
  fix i
  show "propNoL lt le" 
  using wf trans total by (auto simp add: propNoL_def)

  fix p
  from quorum_exists
  show "\<exists>SP. quorum (topology_version p) SP" by simp

  fix S
  assume S: "quorum (topology_version p) S"
  from quorum_finite   S show "finite S" by simp
  from quorum_nonempty S show "S \<noteq> {}" by simp

next
  fix i a p
  assume acc: "accepted i a p"
  from accepts_proposed acc show "proposed i p" by simp
  from accepts_value    acc show "value_accepted i a p = value_proposed i p" by simp

next
  fix i p
  assume "chosen i p"
  with chosen_quorum show "\<exists>S. quorum (topology_version p) S \<and> (\<forall>a\<in>S. accepted i a p)" by simp

next
  fix i a p0 p1
  assume acc: "accepted i a p1"
  assume "promised_free i a p0 \<or> (\<exists>j. j \<sqsubseteq> i \<and> multi_promised j a p0)"
  thus "p0 \<preceq> p1"
  proof (elim disjE exE conjE)
    assume "promised_free i a p0"
    thus ?thesis by (metis promised_free acc)
  next
    fix j assume ji: "j \<sqsubseteq> i" and mp: "multi_promised j a p0"
    thus ?thesis by (metis multi_promised acc)
  qed

next
  fix i a p0 p1
  assume pp: "promised_prev i a p0 p1"
  show "accepted i a p1" by (metis promised_prev_accepted pp)
  show "p1 \<prec> p0" by (metis promised_prev_prev pp)

  fix p2
  assume "accepted i a p2" and "p2 \<prec> p0"
  thus "p1 = p2 \<and> value_accepted i a p1 = value_promised i a p0 \<or> p2 \<prec> p1"
    by (metis promised_prev_max pp)

next
  fix i p
  assume p: "proposed i p"
  show "\<exists>S. quorum (topology_version p) S \<and>
               (\<forall>a\<in>S. (promised_free i a p \<or> (\<exists>j. j \<sqsubseteq> i \<and> multi_promised j a p)) \<or> (\<exists>p1. promised_prev i a p p1))
               \<and> (\<forall>a1\<in>S. \<forall>p1. promised_prev i a1 p p1 \<longrightarrow> value_proposed i p = value_promised i a1 p
                \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2))"
    by (intro proposed_quorum [OF p])

next
  fix i SP SL p0 p1
  assume qSP: "quorum (topology_version p1) SP"
  assume qSL: "quorum (topology_version p0) SL"
  assume chosen: "chosen i p0"
  assume proposed: "proposed i p1"
  assume p01: "p0 \<prec> p1"

  note proposed_topology [OF proposed]
  also note chosen_topology [OF chosen]
  finally have tv10: "topology_version p1 \<le> Suc (topology_version p0)" .

  from p01 have tv01: "topology_version p0 \<le> topology_version p1"
    by (intro topology_version_mono, simp)

  from tv01 tv10 have "topology_version p0 = topology_version p1 \<or> Suc (topology_version p0) = topology_version p1"
    by auto

  thus "SP \<inter> SL \<noteq> {}"
  proof (elim disjE)
    assume eq: "topology_version p0 = topology_version p1"
    show ?thesis
    proof (intro quorum_inter)
      from qSP show "quorum (topology_version p0) SP" by (simp add: eq)
      from qSL show "quorum (topology_version p0) SL" .
    qed
  next
    assume eq: "Suc (topology_version p0) = topology_version p1"
    show ?thesis
    proof (intro quorum_inter_Suc)
      from qSP show "quorum (Suc (topology_version p0)) SP" by (simp add: eq)
      from qSL show "quorum      (topology_version p0)  SL" .
    qed
  qed
qed

theorem (in multiPaxosL)
  assumes "chosen i p1" and "chosen i p2"
  shows multi_paxos_consistent: "value_proposed i p1 = value_proposed i p2"
  using assms by (intro paxosL.paxos_consistent [OF multi_instances])

lemma paxos_empty:
  assumes propNoL: "propNoL lt le"
  assumes no_promise: "\<And> a p p1. \<not>promised_prev a p p1"
  assumes no_promise: "\<And> a p. \<not>promised_free a p"
  assumes no_proposed: "\<And> p. \<not>proposed p"
  assumes no_accepted: "\<And> a p. \<not>accepted a p"
  assumes no_chosen: "\<And> p. \<not>chosen p"

  shows "paxosL lt le quorum_proposer quorum_learner promised_free promised_prev proposed accepted chosen value_promised value_proposed value_accepted"
using assms by (auto simp add: paxosL_def paxosL_axioms_def)

lemma (in paxosL) paxos_propNo [simp]: "propNoL lt le"
using wf trans total by (auto simp add: propNoL_def)

lemma (in paxosL) paxos_add_proposal_free:
  assumes quorum_S: "quorum_proposer quorum S"
  assumes promised_S: "\<And>a. a \<in> S \<Longrightarrow> promised_free a p0"
  shows "paxosL lt le quorum promised_free promised_prev (%p. p = p0 \<or> proposed p) accepted chosen value_promised value_proposed value_accepted"
(* the proposer only needs to know about 'promised' messages to send a 'proposed' message *)
using proposed_quorum promised_free promised_prev_accepted promised_prev_prev promised_prev_max accepts_proposed accepts_value chosen_quorum
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)

  from proposed_quorum
  show "\<forall>p. p = p0 \<or> proposed p \<longrightarrow> (\<exists>S. quorum_proposer quorum S \<and> (\<forall>a\<in>S. promised_free a p \<or> (\<exists> p1. promised_prev a p p1)) 
    \<and> (\<forall>a1\<in>S. \<forall>p1. promised_prev a1 p p1 \<longrightarrow> value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev a2 p p2 \<and> p1 \<prec> p2)))"
    (is "\<forall> p. p = p0 \<or> proposed p \<longrightarrow> ?P p")
  proof (intro allI impI, elim disjE)
    fix p assume pp0: "p = p0"
    show "?P p"
    proof (intro exI [where x = S] conjI ballI allI impI)
      from quorum_S show "quorum_proposer quorum S" .
      fix a1 assume a1S: "a1 \<in> S"
      with promised_S pp0 show "promised_free a1 p \<or> (\<exists>p1. promised_prev a1 p p1)" by auto

      fix p1 assume p1: "promised_prev a1 p p1"
      with promised_S [OF a1S] have False
        by (metis pp0 promised_some_none)
      thus "value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev a2 p p2 \<and> p1 \<prec> p2)" by simp
    qed
  qed simp
qed simp_all


lemma (in paxosL) paxos_add_proposal_constrained:
  assumes quorum_S: "quorum_proposer quorum S"
  assumes promised_S: "\<And>a. a \<in> S \<Longrightarrow> promised_free a p0 \<or> (EX p1. promised_prev a p0 p1)"
  assumes promised_S_value: "\<And>a p1. a \<in> S \<Longrightarrow> promised_prev a p0 p1 \<Longrightarrow> value_proposed p0 = value_promised a p0 \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev a2 p0 p2 \<and> p1 \<prec> p2)"
  shows "paxosL lt le quorum promised_free promised_prev (%p. p = p0 \<or> proposed p) accepted chosen value_promised value_proposed value_accepted"
(* the Proposer only needs to know about promised messages (and 'value') to send a 'proposed' message *)
using proposed_quorum promised_free promised_prev_accepted promised_prev_prev promised_prev_max accepts_proposed accepts_value chosen_quorum
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)
  from proposed_quorum
  show "\<forall>p. p = p0 \<or> proposed p \<longrightarrow> (\<exists>S. quorum_proposer quorum S 
      \<and> (\<forall>a\<in>S. promised_free a p \<or> (\<exists>p1. promised_prev a p p1))
      \<and> (\<forall>a1\<in>S. \<forall>p1. promised_prev a1 p p1 \<longrightarrow> value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev a2 p p2 \<and> p1 \<prec> p2)))"
      (is "\<forall>p. p = p0 \<or> proposed p \<longrightarrow> ?P p")
  proof (intro allI impI, elim disjE)
    fix p assume pp0: "p = p0"
    show "?P p"
    proof (intro exI [where x = S] conjI ballI allI impI)
      from quorum_S show "quorum_proposer quorum S" .
      fix a1 assume a1S: "a1 \<in> S"
      with promised_S pp0 show "promised_free a1 p \<or> (EX p1. promised_prev a1 p p1)" by simp

      fix p1 assume p1: "promised_prev a1 p p1"
      with pp0 have "promised_prev a1 p0 p1" by simp
      from promised_S_value [OF a1S this]
      show "value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev a2 p p2 \<and> p1 \<prec> p2)" by (simp add: pp0)
    qed
  qed simp
qed simp_all

lemma (in paxosL) paxos_add_choice:
  assumes quorum_S: "quorum_learner quorum p0 S"
  assumes accepted_S: "\<And>a. a \<in> S \<Longrightarrow> accepted a p0"
  shows "paxosL lt le quorum promised_free promised_prev proposed accepted (%p. p = p0 \<or> chosen p) value_promised value_proposed value_accepted"
(* the Learner only needs to know about accepted messages to send a 'chosen' message. *)
using proposed_quorum promised_free promised_prev_accepted promised_prev_prev promised_prev_max accepts_proposed accepts_value chosen_quorum
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)
  show "\<forall>p. p = p0 \<or> chosen p \<longrightarrow> (\<exists>S. quorum_learner quorum p S \<and> (\<forall>a\<in>S. accepted a p))"
    by (metis chosen_quorum assms)
qed simp_all

(* the Acceptor only needs to know what it has previously accepted and promised
to send promised messages *)
lemma (in paxosL) paxos_add_promise_free:
  assumes not_accepted: "\<And>p. \<not>accepted a0 p"
  shows   "paxosL lt le quorum (%a p. (a, p) = (a0, p0) \<or> promised_free a p) promised_prev proposed accepted chosen value_promised value_proposed value_accepted"
using proposed_quorum promised_free promised_prev_accepted promised_prev_prev promised_prev_max accepts_proposed accepts_value chosen_quorum
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)
  from assms promised_free
  show "\<forall>a p0a p1. (a, p0a) = (a0, p0) \<or> promised_free a p0a \<longrightarrow> accepted a p1 \<longrightarrow> p0a \<preceq> p1" by simp

  show "\<forall>p. proposed p \<longrightarrow> (\<exists>S. quorum_proposer quorum S
    \<and> (\<forall>a\<in>S. ((a, p) = (a0, p0) \<or> promised_free a p) \<or> (\<exists>p1. promised_prev a p p1))
    \<and> (\<forall>a1\<in>S. \<forall>p1. promised_prev a1 p p1 \<longrightarrow> value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev a2 p p2 \<and> p1 \<prec> p2)))"
      (is "\<forall>p. proposed p \<longrightarrow> ?P p")
  proof (intro allI impI)
    fix p assume proposed: "proposed p"
    with proposed_quorum [OF this] obtain S where S_quorum: "quorum_proposer quorum S"
      and S_accepted: "\<And>a. a \<in> S \<Longrightarrow>  promised_free a p \<or> (\<exists>p1. promised_prev a p p1)"
      and S_consistent: "\<And>a1 p1. \<lbrakk> a1 \<in> S; promised_prev a1 p p1 \<rbrakk> \<Longrightarrow> value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev a2 p p2 \<and> p1 \<prec> p2)" by auto

    from S_quorum
    show "?P p"
    proof (intro exI [where x = S] conjI ballI allI impI)
      fix a1
      assume a1S: "a1 \<in> S"
      from S_accepted [OF this]
      show "((a1, p) = (a0, p0) \<or> promised_free a1 p) \<or> (\<exists>p1. promised_prev a1 p p1)" by auto

      fix p1
      assume promised: "promised_prev a1 p p1"
      from S_consistent [OF a1S promised]
      show "value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev a2 p p2 \<and> p1 \<prec> p2)"
        by auto

    qed simp
  qed
qed auto

lemma (in paxosL) paxos_add_promise_Some:
  assumes accepted: "accepted a0 p'0"
  and accepted_max: "\<And>p2. accepted a0 p2 \<Longrightarrow> p2 \<preceq> p'0"
  and promised_free_newer: "\<And>p. promised_free a0 p \<Longrightarrow> p \<prec> p0"
  and promised_prev_newer: "\<And>p p1. promised_prev a0 p p1 \<Longrightarrow> p \<prec> p0"
  and promised_previous_accepts: "\<And>p2. accepted a0 p2 \<Longrightarrow> p2 \<prec> p0"

  and values_eq: "value_promised a0 p0 = value_accepted a0 p'0"
  shows "paxosL lt le quorum promised_free (%a p p'. (a, p, p') = (a0, p0, p'0) \<or> promised_prev a p p') proposed accepted chosen value_promised value_proposed value_accepted"
using proposed_quorum promised_free promised_prev_accepted promised_prev_prev promised_prev_max accepts_proposed accepts_value chosen_quorum
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)
  show "\<forall>a1 p1 p'1. ((a1, p1, p'1) = (a0, p0, p'0) \<or> promised_prev a1 p1 p'1) \<longrightarrow> accepted a1 p'1"
    by (metis promised_prev_accepted accepted fst_conv snd_conv)
  
  show "\<forall>a1 p1 p'1. (a1, p1, p'1) = (a0, p0, p'0) \<or> promised_prev a1 p1 p'1 \<longrightarrow> p'1 \<prec> p1"
    by (metis accepted fst_conv promised_prev_prev promised_previous_accepts snd_conv)

  show "\<forall>a1 p1 p'1 p2. (a1, p1, p'1) = (a0, p0, p'0) \<or> promised_prev a1 p1 p'1 \<longrightarrow> accepted a1 p2 \<longrightarrow> p2 \<prec> p1 \<longrightarrow> p'1 = p2 \<and> value_accepted a1 p'1 = value_promised a1 p1 \<or> p2 \<prec> p'1"
    by (metis Pair_inject accepted_max promised_prev_max propNo_leE snd_conv values_eq)

  show "\<forall>p. proposed p \<longrightarrow> (\<exists>S. quorum_proposer quorum S
    \<and> (\<forall>a\<in>S. promised_free a p \<or> (\<exists>p1. (a, p, p1) = (a0, p0, p'0) \<or> promised_prev a p p1))
    \<and> (\<forall>a1\<in>S. \<forall>p1. (a1, p, p1) = (a0, p0, p'0) \<or> promised_prev a1 p p1 \<longrightarrow> value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. ((a2, p, p2) = (a0, p0, p'0) \<or> promised_prev a2 p p2) \<and> p1 \<prec> p2)))"
    (is "\<forall>p. proposed p \<longrightarrow> ?P p")
  proof (intro allI impI)
    fix p assume p: "proposed p"
    from proposed_quorum [OF this]
    obtain S where qS: "quorum_proposer quorum S"
      and S_promised: "\<And>a. a \<in> S \<Longrightarrow> promised_free a p \<or> (\<exists>p1. promised_prev a p p1)"
      and S_max: "\<And>a1 p1. \<lbrakk> a1 \<in> S; promised_prev a1 p p1 \<rbrakk> \<Longrightarrow> value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev a2 p p2 \<and> p1 \<prec> p2)" by auto
    show "?P p"
    proof (intro exI [where x = S] conjI ballI allI impI)
      from qS show "quorum_proposer quorum S" .
      fix a1 assume a1S: "a1 \<in> S"
      show "promised_free a1 p \<or> (\<exists>p1. (a1, p, p1) = (a0, p0, p'0) \<or> promised_prev a1 p p1)"
        by (metis S_promised a1S)

      fix p1
      assume "(a1, p, p1) = (a0, p0, p'0) \<or> promised_prev a1 p p1"
      thus "value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. ((a2, p, p2) = (a0, p0, p'0) \<or> promised_prev a2 p p2) \<and> p1 \<prec> p2)"
        by (metis S_max S_promised a1S fst_conv promised_free_newer promised_prev_newer propNo_irreflexive swap_simp)
    qed
  qed
qed simp_all

(* The Acceptor only needs to know about what it's promised and accepted previously to accept a proposal *)
lemma (in paxosL) paxos_add_accepted:
  assumes proposed_p0: "proposed p0"
  assumes promised_free_le: "\<And>p1. promised_free a0 p1 \<Longrightarrow> p1 \<preceq> p0"
  assumes promised_prev_le: "\<And>p1 p2. promised_prev a0 p1 p2 \<Longrightarrow> p1 \<preceq> p0"
  assumes proposed_val: "value_accepted a0 p0 = value_proposed p0"
  shows "paxosL lt le quorum promised_free promised_prev proposed (%a p. (a, p) = (a0, p0) \<or> accepted a p) chosen value_promised value_proposed value_accepted"
using proposed_quorum promised_free promised_prev_accepted promised_prev_prev promised_prev_max accepts_proposed accepts_value chosen_quorum
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)
  show "\<forall>p. chosen p \<longrightarrow> (\<exists>S. quorum_learner quorum p S \<and> (\<forall>a\<in>S. (a, p) = (a0, p0) \<or> accepted a p))"
    (is "\<forall>p. chosen p \<longrightarrow> (\<exists>S. ?P p S)")
    by (metis chosen_quorum)

  show "\<forall>a1 p1 p2. promised_free a1 p1 \<longrightarrow> (a1, p2) = (a0, p0) \<or> accepted a1 p2 \<longrightarrow> p1 \<preceq> p2"
    by (metis prod.sel promised_free_le promised_free)

  show "\<forall>p a. (a, p) = (a0, p0) \<or> accepted a p \<longrightarrow> proposed p"
    by (metis accepts_proposed prod.sel(2) proposed_p0)

  show "\<forall>a1 p1 p2 p3. promised_prev a1 p1 p2 \<longrightarrow> (a1, p3) = (a0, p0) \<or> accepted a1 p3 \<longrightarrow> p3 \<prec> p1 \<longrightarrow> p2 = p3 \<and> value_accepted a1 p2 = value_promised a1 p1 \<or> p3 \<prec> p2"
    apply (intro allI impI, elim disjE)
    apply (metis prod.sel(1) promised_prev_le propNo_leE propNo_lt_not_ge_E swap_simp)
    by (metis promised_prev_max)

  show "\<forall>p a. (a, p) = (a0, p0) \<or> accepted a p \<longrightarrow> value_accepted a p = value_proposed p"
    by (metis accepts_value prod.inject proposed_val)
qed simp_all

lemma (in paxosL) paxos_change_value_promised:
  assumes accepted_eq: "\<And> a p p1. promised_prev a p p1 \<Longrightarrow> value_promised a p = value_promised' a p"
  shows "paxosL lt le quorum promised_free promised_prev proposed accepted chosen value_promised' value_proposed value_accepted"
using assms proposed_quorum promised_free promised_prev_accepted promised_prev_prev promised_prev_max accepts_proposed accepts_value chosen_quorum
  by (unfold paxosL_def paxosL_axioms_def, simp_all)

lemma (in paxosL) paxos_change_value_proposed:
  assumes proposed_eq: "\<And> p. proposed p \<Longrightarrow> value_proposed p = value_proposed' p"
  shows "paxosL lt le quorum promised_free promised_prev proposed accepted chosen value_promised value_proposed' value_accepted"
using assms proposed_quorum promised_free promised_prev_accepted promised_prev_prev promised_prev_max accepts_proposed accepts_value chosen_quorum
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)
  show "\<forall>p. proposed p \<longrightarrow>
        (\<exists>S. quorum_proposer quorum S
        \<and> (\<forall>a\<in>S. promised_free a p \<or> (\<exists>p1. promised_prev a p p1))
        \<and> (\<forall>a1\<in>S. \<forall>p1. promised_prev a1 p p1 \<longrightarrow> value_proposed' p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev a2 p p2 \<and> p1 \<prec> p2)))"
       (is "\<forall>p. proposed p \<longrightarrow> ?P p")
  proof (intro allI impI)
    fix p assume pp: "proposed p"
    from pp proposed_quorum [OF pp]
    show "?P p" by (unfold proposed_eq [OF pp])
  qed

  show "\<forall>p a. accepted a p \<longrightarrow> value_accepted a p = value_proposed' p"
    by (metis accepts_proposed accepts_value proposed_eq)

  from promised_prev_max
  show "\<forall>a p0 p1 p2. promised_prev a p0 p1 \<longrightarrow> accepted a p2 \<longrightarrow> p2 \<prec> p0 \<longrightarrow> p1 = p2 \<and> value_accepted a p1 = value_promised a p0 \<or> p2 \<prec> p1" by simp

qed simp_all

lemma (in paxosL) paxos_change_value_accepted:
  assumes accepted_eq: "\<And> a p. accepted a p \<Longrightarrow> value_accepted a p = value_accepted' a p"
  shows "paxosL lt le quorum promised_free promised_prev proposed accepted chosen value_promised value_proposed value_accepted'"
using assms proposed_quorum promised_free promised_prev_accepted promised_prev_prev promised_prev_max accepts_proposed accepts_value chosen_quorum
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)
  show "\<forall>p a. accepted a p \<longrightarrow> value_accepted' a p = value_proposed p"
    by (metis accepts_value assms)

    from assms
  show "\<forall>a0 p0 p1 p2. promised_prev a0 p0 p1 \<longrightarrow> accepted a0 p2 \<longrightarrow> p2 \<prec> p0 \<longrightarrow> p1 = p2 \<and> value_accepted' a0 p1 = value_promised a0 p0 \<or> p2 \<prec> p1"
    by (metis promised_prev_max)
qed simp_all

lemma (in paxosL) paxos_change_quorum_learner:
  assumes "\<And>p. chosen p \<Longrightarrow> (\<exists>S. quorum_learner quorum' p S \<and> (\<forall>a\<in>S. accepted a p))"
  assumes "quorum_proposer quorum' = quorum_proposer quorum"
  shows "paxosL lt le quorum' promised_free promised_prev proposed accepted chosen value_promised value_proposed value_accepted"
using assms proposed_quorum promised_free promised_prev_accepted promised_prev_prev promised_prev_max accepts_proposed accepts_value chosen_quorum
  by (unfold paxosL_def paxosL_axioms_def, intro conjI, simp_all)

lemma (in paxosL) paxos_change_quorum_unchosen:
  assumes "\<And>p. chosen p \<Longrightarrow> quorum_learner quorum' p = quorum_learner quorum p"
  assumes "quorum_proposer quorum' = quorum_proposer quorum"
  shows "paxosL lt le quorum' promised_free promised_prev proposed accepted chosen value_promised value_proposed value_accepted"
using assms proposed_quorum promised_free promised_prev_accepted promised_prev_prev promised_prev_max accepts_proposed accepts_value chosen_quorum
  by (unfold paxosL_def paxosL_axioms_def, intro conjI, simp_all)

lemma (in paxosL) paxos_change_quorum_superset:
  assumes "quorum_proposer quorum' = quorum_proposer quorum"
  assumes "\<And>p S. \<lbrakk> quorum_learner quorum p S \<rbrakk> \<Longrightarrow> quorum_learner quorum' p S"
  shows "paxosL lt le quorum' promised_free promised_prev proposed accepted chosen value_promised value_proposed value_accepted"
using assms chosen_quorum
  by (intro paxos_change_quorum_learner, simp, metis)

