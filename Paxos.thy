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

lemma
  assumes eq: "\<And>a :: 'aid. f1 a * d1 = f2 a * d2"
  assumes d1: "0 < d1" and d2: "0 < d2"
  shows weighted_majority_mul: "isWeightedMajority f1 = isWeightedMajority f2"
proof (intro ext iffI)
  have p: "\<And>f1 f2 d1 d2 S. isWeightedMajority f1 S \<Longrightarrow> 0 < d1 \<Longrightarrow> 0 < (d2 :: nat) \<Longrightarrow> (\<And>a :: 'aid. f1 a * d1 = f2 a * d2) \<Longrightarrow> isWeightedMajority f2 S"
  proof -
    fix f1 f2 d1 d2 S
    assume eq: "\<And>a :: 'aid. f1 a * d1 = f2 a * (d2 :: nat)"
      and d1: "0 < d1" and d2: "0 < d2"

    hence s0: "\<And> T. {a \<in> T. f2 a \<noteq> 0} = {a \<in> T. f1 a \<noteq> 0}"
      by (metis le0 mult_is_0 not_le)
    
    hence s1: "{a. f2 a \<noteq> 0} = {a. f1 a \<noteq> 0}" by auto

    have d2I: "\<And>n m. d2 * n < d2 * (2 * m) \<Longrightarrow> n < 2 * m"
      by (metis nat_mult_less_cancel_disj)

    have d21: "\<And>T. d2 * setsum f2 T = d1 * setsum f1 T"
    proof -
      fix T
      have "d2 * setsum f2 T = setsum (%n. d2 * f2 n) T" by (simp add: setsum_right_distrib)
      also have "... = setsum (%n. d1 * f1 n) T"
      proof (intro setsum.cong refl)
        fix a
        have "d1 * f1 a = f1 a * d1" by simp
        also note eq
        also have "f2 a * d2 = d2 * f2 a" by simp
        finally show "d2 * f2 a = d1 * f1 a" ..
      qed
      also have "... = d1 * setsum f1 T" by (simp add: setsum_right_distrib)
      finally show "?thesis T" .
    qed

    assume w1: "isWeightedMajority f1 S"
    show "isWeightedMajority f2 S"
    proof (unfold isWeightedMajority.simps weight.simps s0 s1, intro conjI d2I)
      from w1 show "finite {a. f1 a \<noteq> 0}" and "finite S" by auto
      have "d2 * setsum f2 {a \<in> UNIV. f1 a \<noteq> 0} = d1 * setsum f1 {a \<in> UNIV. f1 a \<noteq> 0}"
        by (simp add: d21)
      also from w1 d1 have "... < d1 * (2 * setsum f1 {a \<in> S. f1 a \<noteq> 0})"
        by simp
      also have "... = 2 * (d1 * setsum f1 {a \<in> S. f1 a \<noteq> 0})" by simp
      also from d21 have "... = 2 * (d2 * setsum f2 {a \<in> S. f1 a \<noteq> 0})" by simp
      also have "... = d2 * (2 * setsum f2 {a \<in> S. f1 a \<noteq> 0})" by simp
      finally show "d2 * setsum f2 {a \<in> UNIV. f1 a \<noteq> 0} < ..." .
    qed
  qed

  fix S
  {
    assume "isWeightedMajority f1 S"
    from p [OF this d1 d2 eq]
    show "isWeightedMajority f2 S".
  next
    assume "isWeightedMajority f2 S"
    from p [OF this d2 d1 sym [OF eq]]
    show "isWeightedMajority f1 S".
  }
qed

locale topologyL =

  fixes quorums_seq               :: "'value list \<Rightarrow> ('aid set \<Rightarrow> bool) list"
  assumes quorums_seq_nil:  "quorums_seq [] \<noteq> []"
  assumes quorums_seq_cons: "\<And>v vs. \<exists> qv. quorums_seq (v # vs) = qv @ quorums_seq vs"

  assumes quorum_inter:     "\<And>vs q S1 S2. q \<in> set (quorums_seq vs) \<Longrightarrow> q S1 \<Longrightarrow> q S2 \<Longrightarrow> S1 \<inter> S2 \<noteq> {}"
  assumes quorum_inter_Suc: "\<And>vs tv S1 S2. Suc tv < length (quorums_seq vs) \<Longrightarrow> (quorums_seq vs ! tv) S1 \<Longrightarrow> (quorums_seq vs ! (Suc tv)) S2 \<Longrightarrow> S1 \<inter> S2 \<noteq> {}"
  assumes quorum_finite:    "\<And>vs q S. q \<in> set (quorums_seq vs) \<Longrightarrow> q S  \<Longrightarrow> finite S"
  assumes quorum_nonempty:  "\<And>vs q S. q \<in> set (quorums_seq vs) \<Longrightarrow> q S  \<Longrightarrow> S \<noteq> {}"

  fixes topology_version_increment :: "'value \<Rightarrow> nat"

fun (in topologyL) topology_version :: "'value list \<Rightarrow> nat"
  where
    "topology_version [] = 0"
  | "topology_version (v#vs) = (let vn = topology_version vs; incr = topology_version_increment v
    in (if vn + incr < length (quorums_seq (v#vs)) then vn + incr else vn))"

lemma (in topologyL) topology_version_lt:
  "topology_version vs < length (quorums_seq vs)"
proof (induct vs)
  case (Cons v vs)
  from quorums_seq_cons
  obtain qv where qv: "quorums_seq (v#vs) = qv @ quorums_seq vs" by auto
  show ?case
  apply (simp add: qv Let_def)
    by (metis Cons.hyps trans_less_add2)
qed (simp add: quorums_seq_nil)

lemma (in topologyL) quorums_seq_length_mono: "length (quorums_seq vs0) \<le> length (quorums_seq (vs1 @ vs0))"
proof (induct vs1)
  case Nil thus ?case by simp
next
  case (Cons v vs1)

  from quorums_seq_cons
  obtain qv where qv: "quorums_seq ((v # vs1) @ vs0) = qv @ quorums_seq (vs1 @ vs0)" by auto

  note Cons
  also have "length (quorums_seq (vs1 @ vs0)) \<le> length (quorums_seq ((v # vs1) @ vs0))"
    by (unfold qv, auto)
  finally show ?case .
qed

lemma (in topologyL) take_quorums_seq_append:
  assumes n: "n \<le> length (quorums_seq vs0)"
  shows "take n (rev (quorums_seq vs0)) = take n (rev (quorums_seq (vs1 @ vs0)))"
proof (induct vs1)
  case Nil thus ?case by simp
next
  case (Cons v vs1)
  
  from quorums_seq_cons
  obtain qv where qv: "quorums_seq ((v # vs1) @ vs0) = qv @ quorums_seq (vs1 @ vs0)" by auto

  note n
  also note quorums_seq_length_mono
  finally have n_max: "n \<le> length (quorums_seq (vs1 @ vs0))".

  note Cons
  also have "take n (rev (quorums_seq (vs1 @ vs0))) = take n (rev (quorums_seq ((v # vs1) @ vs0)))"
    by (unfold qv, simp add: n_max)
  finally show ?case .
qed

lemma (in topologyL) take_quorums_seq:
  assumes n: "n \<le> length (quorums_seq vs0)"
  assumes ex1: "EX vs_new. vs1 = vs_new @ vs0"
  assumes ex2: "EX vs_new. vs2 = vs_new @ vs0"
  shows "take n (rev (quorums_seq vs1)) = take n (rev (quorums_seq vs2))"
proof -
  from ex1 obtain vs1' where vs1: "vs1 = vs1' @ vs0" by auto
  from ex2 obtain vs2' where vs2: "vs2 = vs2' @ vs0" by auto
  
  have "take n (rev (quorums_seq vs1)) = take n (rev (quorums_seq vs0))"
    by (unfold vs1, intro sym [OF take_quorums_seq_append] n)
  also have "... = take n (rev (quorums_seq vs2))"
    by (unfold vs2, intro take_quorums_seq_append n)
  finally show ?thesis .
qed

lemma (in topologyL) quorums_seq_nonempty:
  "quorums_seq vs \<noteq> []"
using quorums_seq_nil quorums_seq_cons 
  by (induct vs, simp, metis Nil_is_append_conv)

lemma (in topologyL) topology_version_mono:
  "topology_version vs0 \<le> topology_version (vs1 @ vs0)"
proof (induct vs1)
  case (Cons v vs1)
  note Cons.hyps
  also have "topology_version (vs1 @ vs0) \<le> topology_version ((v # vs1) @ vs0)" by (simp add: Let_def)
  finally show ?case .
qed simp

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

lemma (in paxosL)
  assumes "quorum_learner p0 S"
  assumes "\<And>a. a \<in> S \<Longrightarrow> accepted a p0"
  assumes p0_quorum_inter: "\<And> SP SL p1.
    \<lbrakk> quorum_proposer p1 SP; quorum_learner p0 SL; proposed p1; p0 \<prec> p1 \<rbrakk>
    \<Longrightarrow> SP \<inter> SL \<noteq> {}"
  shows paxos_add_chosen: "paxosL lt le quorum_proposer quorum_learner promised_free promised_prev
  proposed accepted (%p. p = p0 \<or> chosen p) value_promised value_proposed value_accepted"
using accepts_proposed accepts_value chosen_quorum promised_free
  promised_prev_accepted promised_prev_max promised_prev_prev 
  proposed_quorum quorum_finite quorum_inter 
  quorum_nonempty assms
apply unfold_locales
proof -
  fix SP SL p0a p1
  assume "quorum_proposer p1 SP" "quorum_learner p0a SL" "proposed p1" "p0a \<prec> p1" "p0a = p0 \<or> chosen p0a"
  thus "SP \<inter> SL \<noteq> {}" by (metis p0_quorum_inter quorum_inter)
qed auto

fun desc_lt :: "nat \<Rightarrow> nat list"
  where "desc_lt 0 = []"
      | "desc_lt (Suc n) = n # desc_lt n"

lemma desc_lt_seq: "desc_lt n = rev [0 ..< n]" by (induct n, auto)

lemma
  assumes jk: "j \<le> k"
  shows desc_lt_append: "desc_lt k = map (\<lambda>i. i + j) (desc_lt (k - j)) @ desc_lt j"
proof -
  have "map (\<lambda>i. i + j) (desc_lt (k - j)) @ desc_lt j = rev ([0..<j] @ (map (\<lambda>i. i + j) [0..<k - j]))"
    by (simp add: desc_lt_seq rev_map)
  also have "... = rev [0..<k]"
    by (metis add.commute jk le0 le_add_diff_inverse map_add_upt upt_add_eq_append)
  also have "... = desc_lt k" by (simp add: desc_lt_seq)
  finally show "desc_lt k = map (\<lambda>i. i + j) (desc_lt (k - j)) @ desc_lt j"..
qed

locale propTvL = propNoL +
  fixes prop_topology_version          :: "'pid \<Rightarrow> nat"
  assumes prop_topology_version_mono: "\<And>p0 p1. p0 \<preceq> p1 \<Longrightarrow> prop_topology_version p0 \<le> prop_topology_version p1"

locale multiPaxosL
  = p: propNoL lt le
  + t: topologyL quorums_seq topology_version_increment
  + v: propTvL lt le prop_topology_version
  for lt :: "'pid \<Rightarrow> 'pid \<Rightarrow> bool" (infixl "\<prec>" 50) 
  and le :: "'pid \<Rightarrow> 'pid \<Rightarrow> bool" (infixl "\<preceq>" 50)
  and quorums_seq :: "'value list \<Rightarrow> ('aid set \<Rightarrow> bool) list"
  and topology_version_increment :: "'value \<Rightarrow> nat"
  and prop_topology_version :: "'pid \<Rightarrow> nat"
  +

  (* Message predicates *)
  fixes multi_promised :: "nat \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes promised_free  :: "nat \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes promised_prev  :: "nat \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes proposed       :: "nat \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes accepted       :: "nat \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes chosen         :: "nat \<Rightarrow> 'pid \<Rightarrow> bool"

  fixes some_chosen    :: "nat \<Rightarrow> bool"
  defines some_chosen_def: "some_chosen == (%i. EX p. chosen i p)"

  (* Value functions *)
  fixes value_promised :: "nat \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> 'value"
  fixes value_proposed :: "nat \<Rightarrow> 'pid \<Rightarrow> 'value"
  fixes value_accepted :: "nat \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> 'value"

  fixes value_chosen   :: "nat \<Rightarrow> 'value"
  defines value_chosen_def: "value_chosen == (%i. THE v. EX p'. chosen i p' \<and> value_proposed i p' = v)"

  fixes values_lt_list    :: "nat \<Rightarrow> 'value list"
  defines values_lt_list_def: "values_lt_list == (%i. map value_chosen (desc_lt i))"

  fixes instance_topology_version :: "nat \<Rightarrow> nat"
  defines instance_topology_version_def: "instance_topology_version == (%i. topology_version (values_lt_list i))"

  fixes quorum :: "nat \<Rightarrow> 'aid set \<Rightarrow> bool"
  defines quorum_def: "quorum == (%tv. rev (quorums_seq (values_lt_list (SOME i. tv < length (quorums_seq (values_lt_list i))))) ! tv)"

  assumes proposed_quorum:
    "\<And> i p. proposed i p \<Longrightarrow> \<exists> S.
      (quorum (prop_topology_version p) S)
      \<and> (\<forall> a \<in> S. (promised_free i a p 
        \<or> (\<exists>j \<le> i. multi_promised j a p))
        \<or> (\<exists> p1. promised_prev i a p p1))
      \<and> (\<forall> a1 \<in> S. ALL p1. promised_prev i a1 p p1
          \<longrightarrow> value_proposed i p = value_promised i a1 p
          \<or> (\<exists> a2 \<in> S. EX p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2))"

  assumes proposed_topology:
    "\<And> i p. proposed i p \<Longrightarrow> prop_topology_version p \<le> instance_topology_version (GREATEST j. j \<le> i \<and> (\<forall>k < j. some_chosen k))"

  assumes promised_free:
    "\<And> i a p0 p1. \<lbrakk> promised_free i a p0; accepted i a p1 \<rbrakk> \<Longrightarrow> p0 \<preceq> p1"

  assumes multi_promised:
    "\<And>i j a p0 p1. \<lbrakk> multi_promised i a p0; accepted j a p1; i \<le> j \<rbrakk> \<Longrightarrow> p0 \<preceq> p1"

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
    "\<And> i p. chosen i p \<Longrightarrow> EX S. S \<noteq> {} \<and> quorum (prop_topology_version p) S \<and> (ALL a:S. accepted i a p)"

  assumes chosen_topology:
    "\<And> i p. chosen i p \<Longrightarrow> instance_topology_version i \<le> Suc (prop_topology_version p)"

  assumes chosen_Suc: "\<And>i. some_chosen (Suc i) \<Longrightarrow> some_chosen i"

lemma take_mem_eq:
  assumes take_eq: "take (Suc n) xs = take (Suc n) ys"
  shows "xs ! n = ys ! n"
proof -
  have "xs ! n = take (Suc n) xs ! n" by (intro sym [OF nth_take], simp)
  also note take_eq
  also have "take (Suc n) ys ! n = ys ! n" by (intro nth_take, simp)
  finally show ?thesis .
qed

lemma (in multiPaxosL) quorum_topology_version:
  fixes i tv
  assumes le: "tv \<le> instance_topology_version i"
  shows "quorum tv = rev (quorums_seq (values_lt_list i)) ! tv"
proof -
  from le have "tv \<le> topology_version (values_lt_list i)" by (simp add: instance_topology_version_def)
  also note topology_version_lt
  finally have tv_len: "tv < length (quorums_seq (values_lt_list i))" .

  def min_i == "LEAST j. tv < length (quorums_seq (values_lt_list j))"
  from tv_len have le_min: "tv < length (quorums_seq (values_lt_list min_i))"
    by (unfold min_i_def, intro LeastI)

  have values_ex: "\<And>j k. j \<le> k \<Longrightarrow> \<exists>vs_new. values_lt_list k = vs_new @ values_lt_list j"
  proof (intro exI, unfold values_lt_list_def)
    fix j k :: nat
    assume jk: "j \<le> k"
    from desc_lt_append [OF this]
    show "map value_chosen (desc_lt k) = map value_chosen (map (%i. i + j) (desc_lt (k - j))) @ map value_chosen (desc_lt j)"
      by (fold map_append, intro cong [OF refl, where f = "map value_chosen"])
  qed

  show ?thesis
    apply (unfold quorum_def)
    apply (intro take_mem_eq take_quorums_seq [OF _ values_ex values_ex])
  proof -
    from le_min show "Suc tv \<le> length (quorums_seq (values_lt_list min_i))" by simp
    show "min_i \<le> i" by (unfold min_i_def, intro Least_le tv_len)
    from le_min show "min_i \<le> (SOME i. tv < length (quorums_seq (values_lt_list i)))"
      by (unfold min_i_def, intro Least_le someI)
  qed
qed

lemma (in multiPaxosL) chosen_le: "\<And>i. some_chosen i0 \<Longrightarrow> i < i0 \<Longrightarrow> some_chosen i"
proof (induct i0)
  case (Suc j)
  from Suc have "some_chosen (Suc j)" by simp
  from chosen_Suc [OF this] have cj: "some_chosen j" .

  from Suc have "i < j \<or> i = j" by auto
  thus ?case
    by (metis Suc.hyps cj)
qed auto

lemma (in multiPaxosL)
  assumes some_chosen: "some_chosen i"
  shows multi_instances: "paxosL lt le
    (%p S. quorum (prop_topology_version p) S \<and> prop_topology_version p \<le> instance_topology_version i)
    (%p S. quorum (prop_topology_version p) S \<and> prop_topology_version p \<le> instance_topology_version i)
    (%a p. promised_free i a p \<or> (EX j. j \<le> i \<and> multi_promised j a p))
    (promised_prev i) (proposed i) (accepted i) (chosen i)
    (value_promised i) (value_proposed i) (value_accepted i)"
apply unfold_locales
proof -
  fix a p
  assume acc: "accepted i a p"
  from accepts_proposed acc show "proposed i p" by simp
  from accepts_value    acc show "value_accepted i a p = value_proposed i p" by simp

next
  fix p
  assume chosen: "chosen i p"
  from chosen_quorum [OF this]
  obtain S where qS: "quorum (prop_topology_version p) S" and accepted: "\<And>a. a \<in> S \<Longrightarrow> accepted i a p" and nz: "S \<noteq> {}"
    by auto

  from nz obtain a where aS: "a \<in> S" by auto
  from accepts_proposed [OF accepted [OF aS]]
  have proposed: "proposed i p" .

  have "(GREATEST j. j \<le> i \<and> (\<forall>k<j. some_chosen k)) = i"
  proof (intro Greatest_equality conjI allI impI)
    fix k assume ki: "k < i"
    from chosen have "some_chosen i" by (auto simp add: some_chosen_def)
    from chosen_le [OF this ki] show "some_chosen k" .
  qed simp_all
  with proposed_topology [OF proposed]
  have p: "prop_topology_version p \<le> instance_topology_version i" by simp
  
  show "\<exists>S. (quorum (prop_topology_version p) S \<and> prop_topology_version p \<le> instance_topology_version i) \<and> (\<forall>a\<in>S. accepted i a p)"
    by (intro exI [where x = S] conjI ballI accepted qS p chosen allI impI chosen_le [OF some_chosen])

next
  fix a p0 p1
  assume acc: "accepted i a p1"
  assume "promised_free i a p0 \<or> (\<exists>j \<le> i. multi_promised j a p0)"
  thus "p0 \<preceq> p1"
  proof (elim disjE exE conjE)
    assume "promised_free i a p0"
    thus ?thesis by (metis promised_free acc)
  next
    fix j assume ji: "j \<le> i" and mp: "multi_promised j a p0"
    thus ?thesis by (metis multi_promised acc)
  qed

next
  fix a p0 p1
  assume pp: "promised_prev i a p0 p1"
  show "accepted i a p1" by (metis promised_prev_accepted pp)
  show "p1 \<prec> p0" by (metis promised_prev_prev pp)

  fix p2
  assume "accepted i a p2" and "p2 \<prec> p0"
  thus "p1 = p2 \<and> value_accepted i a p1 = value_promised i a p0 \<or> p2 \<prec> p1"
    by (metis promised_prev_max pp)

next
  fix p
  assume p: "proposed i p"
  note proposed_quorum

  have q: "\<And>P Q R. \<exists>a. P a \<and> R a \<Longrightarrow> Q \<Longrightarrow> \<exists>a. (P a \<and> Q) \<and> R a" by metis

  have r: "\<forall>j<i. some_chosen j" by (intro allI impI chosen_le [OF some_chosen])

  from r have i_eq: "(GREATEST j. j \<le> i \<and> (\<forall>k<j. some_chosen k)) = i"
    by (intro Greatest_equality conjI allI impI, auto)

  from proposed_topology [OF p]
  have pi: "prop_topology_version p \<le> instance_topology_version i" by (simp add: i_eq)

  show "\<exists>S. (quorum (prop_topology_version p) S \<and> prop_topology_version p \<le> instance_topology_version i) \<and>
               (\<forall>a\<in>S. (promised_free i a p \<or> (\<exists>j \<le> i. multi_promised j a p)) \<or> (\<exists>p1. promised_prev i a p p1))
               \<and> (\<forall>a1\<in>S. \<forall>p1. promised_prev i a1 p p1 \<longrightarrow> value_proposed i p = value_promised i a1 p
                \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2))"
    by (intro proposed_quorum q p proposed_topology r pi)

next
  {
    fix p
    assume le: "prop_topology_version p \<le> instance_topology_version i"
    have "quorum (prop_topology_version p) \<in> set (rev (quorums_seq (values_lt_list i)))"
    proof (unfold quorum_topology_version [OF le], intro nth_mem)
      from le have "prop_topology_version p \<le> topology_version (values_lt_list i)"
        by (simp add: instance_topology_version_def)
      also note topology_version_lt
      finally show "prop_topology_version p < length (rev (quorums_seq (values_lt_list i)))" by simp
    qed
    hence "quorum (prop_topology_version p) \<in> set (quorums_seq (values_lt_list i))" by simp
  }
  note quorum_mem = this

  {
    fix S p
    assume p: "quorum (prop_topology_version p) S \<and> prop_topology_version p \<le> instance_topology_version i"
    hence q: "quorum (prop_topology_version p) S" and le: "prop_topology_version p \<le> instance_topology_version i" by simp_all
    note mem = quorum_mem [OF le]
  
    show "finite S"
      by (intro quorum_finite [where q = "quorum (prop_topology_version p)" and vs = "values_lt_list i"] mem q)
  
    show "S \<noteq> {}"
      by (intro quorum_nonempty [where q = "quorum (prop_topology_version p)" and vs = "values_lt_list i"] mem q)
  next
    fix SP SL p0 p1
    assume "quorum (prop_topology_version p1) SP \<and> prop_topology_version p1 \<le> instance_topology_version i"
        and "quorum (prop_topology_version p0) SL \<and> prop_topology_version p0 \<le> instance_topology_version i"
    hence qSP: "quorum (prop_topology_version p1) SP" and p1i: "prop_topology_version p1 \<le> instance_topology_version i"
        and qSL: "quorum (prop_topology_version p0) SL" and p0i: "prop_topology_version p0 \<le> instance_topology_version i"
        by simp_all

    note quorum_topology_version [OF p1i]

    assume chosen: "chosen i p0" and proposed: "proposed i p1" and p01: "p0 \<prec> p1"
    have r: "\<forall>j<i. some_chosen j" by (intro allI impI chosen_le [OF some_chosen])

    from r have i_eq: "(GREATEST j. j \<le> i \<and> (\<forall>k<j. some_chosen k)) = i"
      by (intro Greatest_equality conjI allI impI, auto)

    from proposed_topology [OF proposed] have "prop_topology_version p1 \<le> instance_topology_version i"
      by (simp add: i_eq)
    also note chosen_topology [OF chosen]
    finally have tv10: "prop_topology_version p1 \<le> Suc (prop_topology_version p0)" .
  
    from p01 have tv01: "prop_topology_version p0 \<le> prop_topology_version p1"
      by (intro prop_topology_version_mono, simp)
  
    from tv01 tv10 have "prop_topology_version p0 = prop_topology_version p1 \<or> Suc (prop_topology_version p0) = prop_topology_version p1"
      by auto

    thus "SP \<inter> SL \<noteq> {}"
    proof (elim disjE)
      assume eq: "prop_topology_version p0 = prop_topology_version p1"
      show ?thesis
        by (intro quorum_inter [OF quorum_mem [OF p0i]] qSL, unfold eq, intro qSP)
    next
      assume eq: "Suc (prop_topology_version p0) = prop_topology_version p1"
      show ?thesis
      proof (intro quorum_inter_Suc)
        have prop_p1_lt_len: "prop_topology_version p1 < length (quorums_seq (values_lt_list i))"
        proof -
          from p1i have "prop_topology_version p1 \<le> topology_version (values_lt_list i)"
            by (simp add: instance_topology_version_def)
          also note topology_version_lt
          finally show ?thesis . 
        qed

        note quorum_topology_version [OF p1i]
        also have "rev (quorums_seq (values_lt_list i)) ! prop_topology_version p1 = quorums_seq (values_lt_list i) ! (length (quorums_seq (values_lt_list i) ) - Suc (prop_topology_version p1))"
          by (intro rev_nth prop_p1_lt_len)
        finally have "quorum (prop_topology_version p1) = quorums_seq (values_lt_list i) ! (length (quorums_seq (values_lt_list i)) - Suc (prop_topology_version p1))" .
        with qSP show "(quorums_seq (values_lt_list i) ! (length (quorums_seq (values_lt_list i)) - Suc (prop_topology_version p1))) SP" by simp

        from prop_p1_lt_len
        have Suc_Suc_eq: "Suc (length (quorums_seq (values_lt_list i)) - Suc (prop_topology_version p1)) = length (quorums_seq (values_lt_list i)) - prop_topology_version p1" by auto

        note quorum_topology_version [OF p0i]
        also have "rev (quorums_seq (values_lt_list i)) ! prop_topology_version p0 = quorums_seq (values_lt_list i) ! (length (quorums_seq (values_lt_list i) ) - Suc (prop_topology_version p0))"
        proof (intro rev_nth)
          from p0i have "prop_topology_version p0 \<le> topology_version (values_lt_list i)"
            by (simp add: instance_topology_version_def)
          also note topology_version_lt
          finally show "prop_topology_version p0 < length (quorums_seq (values_lt_list i))" .
        qed
        finally have "quorum (prop_topology_version p0) = quorums_seq (values_lt_list i) ! (Suc (length (quorums_seq (values_lt_list i)) - Suc (prop_topology_version p1)))"
          by (simp add: eq Suc_Suc_eq)

        with qSL show "(quorums_seq (values_lt_list i) ! Suc (length (quorums_seq (values_lt_list i)) - Suc (prop_topology_version p1))) SL" by simp
        
        from quorums_seq_nonempty have nz: "0 < length (quorums_seq (values_lt_list i))" by simp

        from prop_p1_lt_len eq
        have "Suc (length (quorums_seq (values_lt_list i)) - Suc (prop_topology_version p1)) = length (quorums_seq (values_lt_list i)) - Suc (prop_topology_version p0)"
          by auto
        also from nz have "... < length (quorums_seq (values_lt_list i))" by auto
        finally show "Suc (length (quorums_seq (values_lt_list i)) - Suc (prop_topology_version p1)) < length (quorums_seq (values_lt_list i))" .
      qed
    qed
  }
qed

theorem (in multiPaxosL)
  assumes "chosen i p1" and "chosen i p2"
  shows multi_paxos_consistent: "value_proposed i p1 = value_proposed i p2"
  using assms by (intro paxosL.paxos_consistent [OF multi_instances], auto simp add: some_chosen_def)

lemma (in multiPaxosL) multiPaxos_the_value:
  assumes c: "chosen i p"
  shows "value_chosen i = value_proposed i p"
proof (unfold value_chosen_def, rule theI2)
  from c
  show "\<exists>p'. chosen i p' \<and> value_proposed i p' = value_proposed i p" by auto

  fix v
  assume "\<exists>p'. chosen i p' \<and> value_proposed i p' = v"
  then obtain p' where c': "chosen i p'"
    and v: "v = value_proposed i p'" by auto

  note v
  also have "value_proposed i p' = value_proposed i p"
    by (intro multi_paxos_consistent c c')
  finally show "v = value_proposed i p" .
  thus "v = value_proposed i p" .
qed

lemma paxos_empty:
  assumes "propNoL lt le"
  assumes "topologyL quorums_seq"
  assumes "propTvL lt le prop_topology_version"

  assumes "\<And> i a p p1. \<not>promised_prev i a p p1"
  assumes "\<And> i a p. \<not>promised_free i a p"
  assumes "\<And> i p. \<not>proposed i p"
  assumes "\<And> i a p. \<not>accepted i a p"
  assumes "\<And> i p. \<not>chosen i p"

  shows "multiPaxosL lt le quorums_seq topology_version_increment prop_topology_version multi_promised promised_free promised_prev proposed accepted chosen value_promised value_proposed value_accepted"
using assms by (unfold_locales, auto simp add: propNoL_def topologyL_def propTvL_def propTvL_axioms_def)

lemma (in multiPaxosL) multiPaxos_intro_simple:

  assumes proposed_quorum:
   "\<And> i p . proposed' i p \<Longrightarrow> \<exists> S.
      (quorum (prop_topology_version p) S)
      \<and> (\<forall> a \<in> S. (promised_free' i a p 
        \<or> (\<exists>j \<le> i. multi_promised' j a p))
        \<or> (\<exists> p1. promised_prev' i a p p1))
      \<and> (\<forall> a1 \<in> S. ALL p1. promised_prev' i a1 p p1
          \<longrightarrow> value_proposed i p = value_promised' i a1 p
          \<or> (\<exists> a2 \<in> S. EX p2. promised_prev' i a2 p p2 \<and> p1 \<prec> p2))"

  assumes proposed_topology:
    "\<And> i p. proposed' i p
      \<Longrightarrow> prop_topology_version p \<le> instance_topology_version (GREATEST j. j \<le> i \<and> (\<forall>k < j. some_chosen k))"

  assumes promised_free:
    "\<And> i a p0 p1. \<lbrakk> promised_free' i a p0; accepted' i a p1 \<rbrakk> \<Longrightarrow> p0 \<preceq> p1"

  assumes multi_promised:
    "\<And>i j a p0 p1. \<lbrakk> multi_promised' i a p0; accepted' j a p1; i \<le> j \<rbrakk> \<Longrightarrow> p0 \<preceq> p1"

  assumes promised_prev_accepted:
    "\<And> i a p0 p1. promised_prev' i a p0 p1 \<Longrightarrow> accepted' i a p1"
  assumes promised_prev_prev:
    "\<And> i a p0 p1. promised_prev' i a p0 p1 \<Longrightarrow> p1 \<prec> p0"
  assumes promised_prev_max:
    "\<And> i a p0 p1 p2. \<lbrakk> promised_prev' i a p0 p1; accepted' i a p2; p2 \<prec> p0 \<rbrakk>
      \<Longrightarrow> ((p1 = p2 \<and> value_accepted' i a p1 = value_promised' i a p0) \<or> p2 \<prec> p1)"

  assumes accepts_proposed:
    "\<And> i p a. accepted' i a p \<Longrightarrow> proposed' i p"
  assumes accepts_value:
    "\<And> i p a. accepted' i a p \<Longrightarrow> value_accepted' i a p = value_proposed i p"

  assumes chosen_quorum:
    "\<And> i p. chosen i p \<Longrightarrow> EX S. S \<noteq> {} \<and> quorum (prop_topology_version p) S \<and> (ALL a:S. accepted' i a p)"

  shows "multiPaxosL lt le quorums_seq topology_version_increment prop_topology_version
  multi_promised' promised_free' promised_prev' proposed' accepted' chosen
  value_promised' value_proposed value_accepted'"
using assms chosen_topology chosen_Suc
apply unfold_locales
  by (simp_all add: quorum_def values_lt_list_def value_chosen_def instance_topology_version_def some_chosen_def)

lemma (in multiPaxosL) multiPaxos_add_proposal_free:
  assumes quorum_S: "quorum (prop_topology_version p0) S"
  assumes promised_S: "\<And>a. a \<in> S \<Longrightarrow> promised_free i0 a p0 \<or> (\<exists>j \<le> i0. multi_promised j a p0)"
  assumes topo_version: "prop_topology_version p0 \<le> instance_topology_version i1"
  assumes i10: "i1 \<le> i0"
  assumes i1_chosen: "\<And>j. j < i1 \<Longrightarrow> some_chosen j"
  shows "multiPaxosL lt le quorums_seq topology_version_increment prop_topology_version
  multi_promised promised_free promised_prev
  (%i p. (i,p) = (i0,p0) \<or> proposed i p)
  accepted chosen value_promised value_proposed value_accepted"
(* the proposer only needs to know about 'promised' messages to send a 'proposed' message *)
using accepts_proposed accepts_value chosen_Suc chosen_quorum
  chosen_topology multi_promised promised_free
  promised_prev_accepted promised_prev_max promised_prev_prev
  proposed_quorum proposed_topology  quorum_finite
  quorum_inter quorum_inter_Suc quorum_nonempty 
  quorums_seq_nonempty assms
apply (intro multiPaxos_intro_simple)
proof -
  fix i p
  assume ip: "(i, p) = (i0, p0) \<or> proposed i p"
  with proposed_quorum show "(\<exists>S. quorum (prop_topology_version p) S \<and>
               (\<forall>a\<in>S. (promised_free i a p \<or> (\<exists>j \<le> i. multi_promised j a p))
                    \<or> (\<exists>p1. promised_prev i a p p1)) \<and> (\<forall>a1\<in>S. \<forall>p1. promised_prev i a1 p p1
                    \<longrightarrow> value_proposed i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2)))"
  proof (elim disjE)
    assume ip: "(i, p) = (i0, p0)"
    show "?thesis"
    proof (intro exI [where x = S] conjI ballI allI impI)
      from ip quorum_S show "quorum (prop_topology_version p) S" by simp
      fix a1 assume "a1 \<in> S"
      note a1S = promised_S [OF this]
      
      with ip
      show "(promised_free i a1 p \<or> (\<exists>j \<le> i. multi_promised j a1 p)) \<or> (\<exists>p1. promised_prev i a1 p p1)"
        by simp

      fix p1
      assume prev: "promised_prev i a1 p p1"
      have not_free: "~promised_free i a1 p"
        by (metis prev promised_free promised_prev_accepted promised_prev_prev propNo_leE propNo_lt_not_ge_E)
      
      have not_multi: "\<And>j. j \<le> i \<Longrightarrow> ~multi_promised j a1 p"
        by (metis multi_promised prev promised_prev_accepted promised_prev_prev propNo_lt_not_ge_E propNo_trans_lt_le)

      from a1S ip have "promised_free i a1 p \<or> (\<exists>j \<le> i. multi_promised j a1 p)" by simp
      with not_free not_multi
      show "value_proposed i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2)" by auto
    qed
  qed simp

  from ip
  show "prop_topology_version p \<le> instance_topology_version (GREATEST j. j \<le> i \<and> (\<forall>k<j. some_chosen k))"
  proof (elim disjE)
    (* TODO *)
  note proposed_topology

  assume "\<forall>j<i. some_chosen j"
  with ip have "prop_topology_version p \<le> instance_topology_version i"
    by (metis prod.sel proposed_topology topo_version)

qed simp_all

lemma (in multiPaxosL) multiPaxos_add_proposal_constrained:
  assumes quorum_S: "quorum (prop_topology_version p0) S"
  assumes promised_S: "\<And>a. a \<in> S \<Longrightarrow> promised_free i0 a p0 \<or> (\<exists>j \<le> i0. multi_promised j a p0) \<or> (EX p1. promised_prev i0 a p0 p1)"
  assumes promised_S_value: "\<And>a p1. a \<in> S \<Longrightarrow> promised_prev i0 a p0 p1 \<Longrightarrow> value_proposed i0 p0 = value_promised i0 a p0 \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i0 a2 p0 p2 \<and> p1 \<prec> p2)"
  assumes topo_version: "prop_topology_version p0 \<le> instance_topology_version i0"
  shows "multiPaxosL lt le quorums_seq topology_version_increment prop_topology_version
  multi_promised promised_free promised_prev
  (%i p. (i,p) = (i0,p0) \<or> proposed i p)
  accepted chosen value_promised value_proposed value_accepted"
(* the Proposer only needs to know about promised messages (and 'value') to send a 'proposed' message *)
using accepts_proposed accepts_value chosen_Suc chosen_quorum
  chosen_topology multi_promised promised_free
  promised_prev_accepted promised_prev_max promised_prev_prev
  proposed_quorum proposed_topology  quorum_finite
  quorum_inter quorum_inter_Suc quorum_nonempty 
  quorums_seq_nonempty assms
apply (intro multiPaxos_intro_simple)
proof -
  from proposed_quorum
  show "\<And>i p. (i, p) = (i0, p0) \<or> proposed i p \<Longrightarrow>
          (\<exists>S. quorum (prop_topology_version p) S \<and>
               (\<forall>a\<in>S. (promised_free i a p \<or>
                (\<exists>j \<le> i. multi_promised j a p))
                \<or> (\<exists>p1. promised_prev i a p p1)) \<and> (\<forall>a1\<in>S. \<forall>p1. promised_prev i a1 p p1
                \<longrightarrow> value_proposed i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2)))"
      (is "\<And> i p. (i,p) = (i0,p0) \<or> proposed i p \<Longrightarrow> ?P i p")
  proof (elim disjE)
    fix i p assume ip: "(i,p) = (i0,p0)"
    show "?P i p"
    proof (intro exI [where x = S] conjI ballI allI impI)
      from quorum_S ip show "quorum (prop_topology_version p) S" by simp
      fix a1 assume a1S: "a1 \<in> S"
      with promised_S ip show "(promised_free i a1 p \<or> (\<exists> j \<le> i. multi_promised j a1 p)) \<or> (\<exists>p1. promised_prev i a1 p p1)" by simp

      fix p1 assume p1: "promised_prev i a1 p p1"
      with ip have "promised_prev i0 a1 p0 p1" by simp
      from promised_S_value [OF a1S this] ip
      show "value_proposed i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2)" by simp
    qed
  qed simp
qed auto

(* the Acceptor only needs to know what it has previously accepted and promised
to send promised messages *)
lemma (in multiPaxosL) multiPaxos_add_promise_free:
  assumes not_accepted: "\<And>p. \<not>accepted i0 a0 p"
  shows "multiPaxosL lt le quorums_seq topology_version_increment prop_topology_version
  multi_promised
  (%i a p. (i, a, p) = (i0, a0, p0) \<or> promised_free i a p)
  promised_prev proposed accepted chosen value_promised value_proposed value_accepted"
using accepts_proposed accepts_value chosen_Suc chosen_quorum
  chosen_topology multi_promised promised_free
  promised_prev_accepted promised_prev_max promised_prev_prev
  proposed_quorum proposed_topology  quorum_finite
  quorum_inter quorum_inter_Suc quorum_nonempty 
  quorums_seq_nonempty assms
apply (intro multiPaxos_intro_simple)
proof -
  fix i p assume proposed: "proposed i p"
  from proposed_quorum [OF this] obtain S where S_quorum: "quorum (prop_topology_version p) S"
    and S_accepted: "\<And>a. a \<in> S \<Longrightarrow> (promised_free i a p \<or> (\<exists>j \<le> i. multi_promised j a p)) \<or> (\<exists>p1. promised_prev i a p p1)"
    and S_consistent: "\<And>a1 p1. \<lbrakk> a1 \<in> S; promised_prev i a1 p p1 \<rbrakk>
      \<Longrightarrow> value_proposed i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2)" by auto

  from S_quorum
  show "\<exists>S. quorum (prop_topology_version p) S \<and>
               (\<forall>a\<in>S. (((i, a, p) = (i0, a0, p0) \<or> promised_free i a p) \<or> (\<exists>j \<le> i. multi_promised j a p)) \<or> (\<exists>p1. promised_prev i a p p1)) \<and>
               (\<forall>a1\<in>S. \<forall>p1. promised_prev i a1 p p1 \<longrightarrow> value_proposed i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2))"
  proof (intro exI [where x = S] conjI ballI allI impI)
    fix a1
    assume a1S: "a1 \<in> S"
    from S_accepted [OF this]
    show "(((i, a1, p) = (i0, a0, p0) \<or> promised_free i a1 p) \<or> (\<exists>j \<le> i. multi_promised j a1 p)) \<or> (\<exists>p1. promised_prev i a1 p p1)" by auto

    fix p1
    assume promised: "promised_prev i a1 p p1"
    from S_consistent [OF a1S promised]
    show "value_proposed i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2)"
      by auto

  qed simp

next
  fix i a p0a p1
  assume "(i, a, p0a) = (i0, a0, p0) \<or> promised_free i a p0a" and "accepted i a p1"
  thus "p0a \<preceq> p1" by (metis not_accepted prod.sel promised_free)
qed simp_all

(* the Acceptor only needs to know what it has previously accepted and promised
to send promised messages *)
lemma (in multiPaxosL) multiPaxos_add_multi_promise:
  assumes not_accepted: "\<And>p j. i0 \<le> j \<Longrightarrow> \<not>accepted j a0 p"
  shows "multiPaxosL lt le quorums_seq topology_version_increment prop_topology_version
  (%i a p. (i, a, p) = (i0, a0, p0) \<or> multi_promised i a p)
  promised_free promised_prev proposed accepted chosen value_promised value_proposed value_accepted"
using accepts_proposed accepts_value chosen_Suc chosen_quorum
  chosen_topology multi_promised promised_free
  promised_prev_accepted promised_prev_max promised_prev_prev
  proposed_quorum proposed_topology  quorum_finite
  quorum_inter quorum_inter_Suc quorum_nonempty 
  quorums_seq_nonempty assms
apply (intro multiPaxos_intro_simple)
proof -
  fix i j a p0a p1
  assume "(i, a, p0a) = (i0, a0, p0) \<or> multi_promised i a p0a" and "accepted j a p1" and "i \<le> j"
  thus "p0a \<preceq> p1" by (metis not_accepted prod.sel multi_promised)
next

  fix i p assume proposed: "proposed i p"
  from proposed_quorum [OF this] obtain S where S_quorum: "quorum (prop_topology_version p) S"
    and S_accepted: "\<And>a. a \<in> S \<Longrightarrow> (promised_free i a p \<or> (\<exists>j \<le> i. multi_promised j a p)) \<or> (\<exists>p1. promised_prev i a p p1)"
    and S_consistent: "\<And>a1 p1. \<lbrakk> a1 \<in> S; promised_prev i a1 p p1 \<rbrakk>
      \<Longrightarrow> value_proposed i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2)" by auto

  from S_quorum
  show "\<exists>S. quorum (prop_topology_version p) S \<and>
               (\<forall>a\<in>S. (promised_free i a p \<or> (\<exists>j \<le> i. ((j, a, p) = (i0, a0, p0) \<or> multi_promised j a p))) \<or> (\<exists>p1. promised_prev i a p p1)) \<and>
               (\<forall>a1\<in>S. \<forall>p1. promised_prev i a1 p p1 \<longrightarrow> value_proposed i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2))"
  proof (intro exI [where x = S] conjI ballI allI impI)
    fix a1
    assume a1S: "a1 \<in> S"
    from S_accepted [OF this]
    show "(promised_free i a1 p \<or> (\<exists>j \<le> i. ((j, a1, p) = (i0, a0, p0) \<or> multi_promised j a1 p))) \<or> (\<exists>p1. promised_prev i a1 p p1)" by auto

    fix p1
    assume promised: "promised_prev i a1 p p1"
    from S_consistent [OF a1S promised]
    show "value_proposed i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2)"
      by auto
  qed simp
qed simp_all

lemma (in multiPaxosL) multiPaxos_add_promise_prev:
  assumes accepted: "accepted i0 a0 p'0"
  assumes accepted_max: "\<And>p2. accepted i0 a0 p2 \<Longrightarrow> p2 \<preceq> p'0"
  and lt: "p'0 \<prec> p0"
  and values_eq: "value_promised i0 a0 p0 = value_accepted i0 a0 p'0"

  shows "multiPaxosL lt le quorums_seq topology_version_increment prop_topology_version
  multi_promised promised_free
  (%i a p p'. (i,a,p,p') = (i0, a0, p0, p'0) \<or> promised_prev i a p p')
  proposed accepted chosen value_promised value_proposed value_accepted"
using accepts_proposed accepts_value chosen_Suc chosen_quorum
  chosen_topology multi_promised promised_free
  promised_prev_accepted promised_prev_max promised_prev_prev
  proposed_quorum proposed_topology  quorum_finite
  quorum_inter quorum_inter_Suc quorum_nonempty 
  quorums_seq_nonempty assms
apply (intro multiPaxos_intro_simple)
proof -
  fix i a p p' p2
  assume eq: "(i, a, p, p') = (i0, a0, p0, p'0) \<or> promised_prev i a p p'" and acc: "accepted i a p2" and p2p: "p2 \<prec> p"
  with promised_prev_max
  show "p' = p2 \<and> value_accepted i a p' = value_promised i a p \<or> p2 \<prec> p'"
  proof (elim disjE)
    assume eq: "(i, a, p, p') = (i0, a0, p0, p'0)"
    from acc eq have "p2 \<preceq> p'0" by (intro accepted_max, simp)
    hence "p2 = p'0 \<or> p2 \<prec> p'0" by auto
    with eq show "p' = p2 \<and> value_accepted i a p' = value_promised i a p \<or> p2 \<prec> p'"
      by (elim disjE, simp_all add: values_eq)
  qed simp
next
  fix i p
  assume proposed: "proposed i p"
  from proposed_quorum [OF this] obtain S where S_quorum: "quorum (prop_topology_version p) S"
    and S_promised: "\<And>a. a \<in> S \<Longrightarrow> (promised_free i a p \<or> (\<exists>j \<le> i. multi_promised j a p)) \<or> (\<exists>p1. promised_prev i a p p1)"
    and S_max: "\<And>a1 p1. \<lbrakk> a1 \<in> S; promised_prev i a1 p p1 \<rbrakk>
      \<Longrightarrow> value_proposed i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2)" by auto
  from S_quorum
  show "(\<exists>S. quorum (prop_topology_version p) S \<and>
               (\<forall>a\<in>S. (promised_free i a p \<or> (\<exists>j \<le> i. multi_promised j a p)) \<or> (\<exists>p1. (i, a, p, p1) = (i0, a0, p0, p'0) \<or> promised_prev i a p p1)) \<and>
               (\<forall>a1\<in>S. \<forall>p1. (i, a1, p, p1) = (i0, a0, p0, p'0) \<or> promised_prev i a1 p p1 \<longrightarrow> value_proposed i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. ((i, a2, p, p2) = (i0, a0, p0, p'0) \<or> promised_prev i a2 p p2) \<and> p1 \<prec> p2)))"
  proof (intro exI [where x = S] conjI ballI allI impI)
    fix a1 assume a1S: "a1 \<in> S"
    from S_promised [OF this]
    show "(promised_free i a1 p \<or> (\<exists>j \<le> i. multi_promised j a1 p)) \<or> (\<exists>p1. (i, a1, p, p1) = (i0, a0, p0, p'0) \<or> promised_prev i a1 p p1)" by auto
    
    fix p1
    assume "(i, a1, p, p1) = (i0, a0, p0, p'0) \<or> promised_prev i a1 p p1" (is "?A \<or> ?B")
    thus "value_proposed i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. ((i, a2, p, p2) = (i0, a0, p0, p'0) \<or> promised_prev i a2 p p2) \<and> p1 \<prec> p2)"
    proof (elim disjE)
      assume "?B"
      from S_max [OF a1S this]
      show ?thesis by auto
    next
      assume "?A"
      hence eq: "i = i0" "a1 = a0" "p = p0" "p1 = p'0" by simp_all

      note accepted_max
      also note lt
      finally have promised_previous_accepts: "\<And>p2. accepted i0 a0 p2 \<Longrightarrow> p2 \<prec> p0" .

      from S_promised [OF a1S]
      have "(promised_free i0 a0 p0 \<or> (\<exists>j \<le> i0. multi_promised j a0 p0)) \<or> (\<exists>p1. promised_prev i0 a0 p0 p1)"
        by (unfold eq)

      thus ?thesis
      proof (elim disjE exE conjE)
        assume p: "promised_free i0 a0 p0"
        note promised_free [OF p accepted] 
        also note promised_previous_accepts [OF accepted]
        finally show ?thesis by simp
      next
        fix j
        assume ji: "j \<le> i0" and p: "multi_promised j a0 p0"
        note multi_promised [OF p accepted ji]
        also note promised_previous_accepts [OF accepted]
        finally show ?thesis by simp
      next
        fix p'
        assume p: "promised_prev i0 a0 p0 p'"
        with eq show ?thesis
          by (metis S_max a1S accepted p promised_prev_max promised_previous_accepts)
      qed
    qed
  qed
next
  fix i a p0a p1
  assume a: "p'0 \<prec> p0" "value_promised i0 a0 p0 = value_accepted i0 a0 p'0" "(i, a, p0a, p1) = (i0, a0, p0, p'0) \<or> promised_prev i a p0a p1"
  from a show "p1 \<prec> p0a" by (metis prod.sel(1) promised_prev_prev swap_simp)
  from a show "accepted i a p1" by (metis accepted prod.sel(1) prod.sel(2) promised_prev_accepted)
qed simp_all

(* The Acceptor only needs to know about what it's promised previously to accept a proposal *)
lemma (in multiPaxosL) multiPaxos_add_accepted:
  assumes proposed_p0: "proposed i0 p0"
  assumes promised_free_le: "\<And>p1. promised_free i0 a0 p1 \<Longrightarrow> p1 \<preceq> p0"
  assumes promised_prev_le: "\<And>p1 p2. promised_prev i0 a0 p1 p2 \<Longrightarrow> p1 \<preceq> p0"
  assumes multi_promised_le: "\<And>j p1. multi_promised j a0 p1 \<Longrightarrow> j \<le> i0 \<Longrightarrow> p1 \<preceq> p0"
  assumes proposed_val: "value_accepted i0 a0 p0 = value_proposed i0 p0"

  shows "multiPaxosL lt le quorums_seq topology_version_increment prop_topology_version
  multi_promised promised_free promised_prev proposed
  (%i a p. (i,a,p) = (i0, a0, p0) \<or> accepted i a p)
  chosen value_promised value_proposed value_accepted"
using accepts_proposed accepts_value chosen_Suc chosen_quorum
  chosen_topology multi_promised promised_free
  promised_prev_accepted promised_prev_max promised_prev_prev
  proposed_quorum proposed_topology  quorum_finite
  quorum_inter quorum_inter_Suc quorum_nonempty 
  quorums_seq_nonempty assms
apply (intro multiPaxos_intro_simple)
proof -
  fix i a p1 p0a
  assume a: "value_accepted i0 a0 p0 = value_proposed i0 p0" "(i, a, p1) = (i0, a0, p0) \<or> accepted i a p1"
  {
    assume "promised_free i a p0a"
    with a show "p0a \<preceq> p1" by (metis prod.sel promised_free promised_free_le)
  next
    fix j assume "multi_promised j a p0a" "j \<le> i"
    with a show "p0a \<preceq> p1" by (metis prod.sel multi_promised multi_promised_le)
  next
    fix p2 assume "promised_prev i a p0a p2" "p1 \<prec> p0a"
    with a show "p2 = p1 \<and> value_accepted i a p2 = value_promised i a p0a \<or> p1 \<prec> p2"
      by (metis prod.sel promised_prev_le promised_prev_max propNo_leE propNo_lt_not_ge_E)
  }
next
  fix i p a
  assume a: "value_accepted i0 a0 p0 = value_proposed i0 p0" "(i, a, p) = (i0, a0, p0) \<or> accepted i a p"
  from a show "proposed i p" by (metis prod.sel accepts_proposed proposed_p0)
  from a show "value_accepted i a p = value_proposed i p" by (metis prod.sel accepts_value)
next
  fix i p
  assume "chosen i p"
  thus "(\<exists>S. S \<noteq> {} \<and> quorum (prop_topology_version p) S \<and> (\<forall>a\<in>S. (i, a, p) = (i0, a0, p0) \<or> accepted i a p))"
    by (metis chosen_quorum)
qed simp_all

lemma (in multiPaxosL) multiPaxos_change_value_promised:
  assumes accepted_eq: "\<And> i a p p1. promised_prev i a p p1 \<Longrightarrow> value_promised i a p = value_promised' i a p"

  shows "multiPaxosL lt le quorums_seq topology_version_increment prop_topology_version
  multi_promised promised_free promised_prev proposed accepted
  chosen value_promised' value_proposed value_accepted"
using accepts_proposed accepts_value chosen_Suc chosen_quorum
  chosen_topology multi_promised promised_free
  promised_prev_accepted promised_prev_max promised_prev_prev
  proposed_quorum proposed_topology  quorum_finite
  quorum_inter quorum_inter_Suc quorum_nonempty 
  quorums_seq_nonempty assms
apply (intro multiPaxos_intro_simple)
  by simp_all

lemma (in multiPaxosL) multiPaxos_change_value_accepted:
  assumes accepted_eq: "\<And> i a p. accepted i a p \<Longrightarrow> value_accepted i a p = value_accepted' i a p"

  shows "multiPaxosL lt le quorums_seq topology_version_increment prop_topology_version
  multi_promised promised_free promised_prev proposed accepted
  chosen value_promised value_proposed value_accepted'"
using accepts_proposed accepts_value chosen_Suc chosen_quorum
  chosen_topology multi_promised promised_free
  promised_prev_accepted promised_prev_max promised_prev_prev
  proposed_quorum proposed_topology  quorum_finite
  quorum_inter quorum_inter_Suc quorum_nonempty 
  quorums_seq_nonempty assms
apply (intro multiPaxos_intro_simple)
  by simp_all


lemma (in multiPaxosL) multiPaxos_intro:

  assumes defns:
    "\<And>i. some_chosen' i = (EX p. chosen' i p)"
    "value_chosen' = (%i. THE v. EX p. chosen' i p \<and> value_proposed' i p = v)"
    "\<And>i. values_lt_list' i = map value_chosen' (desc_lt i)"
    "\<And>i. instance_topology_version' i = topology_version (values_lt_list' i)"
    "\<And>tv. quorum' tv = rev (quorums_seq (values_lt_list' (SOME i. tv < length (quorums_seq (values_lt_list' i))))) ! tv"

  assumes proposed_quorum:
    "\<And> i p . proposed i p \<Longrightarrow> \<exists> S.
      (quorum' (prop_topology_version p) S)
      \<and> (\<forall> a \<in> S. (promised_free i a p 
        \<or> (\<exists>j \<le> i. multi_promised j a p))
        \<or> (\<exists> p1. promised_prev i a p p1))
      \<and> (\<forall> a1 \<in> S. ALL p1. promised_prev i a1 p p1
          \<longrightarrow> value_proposed' i p = value_promised i a1 p
          \<or> (\<exists> a2 \<in> S. EX p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2))"

  assumes proposed_topology:
    "\<And> i p. proposed i p 
      \<Longrightarrow> \<forall>j < i. some_chosen' j
      \<Longrightarrow> prop_topology_version p \<le> instance_topology_version' i"

  assumes accepts_value:
    "\<And> i p a. accepted i a p \<Longrightarrow> value_accepted i a p = value_proposed' i p"

  assumes chosen_quorum:
    "\<And> i p. chosen' i p \<Longrightarrow> EX S. S \<noteq> {} \<and> quorum' (prop_topology_version p) S \<and> (ALL a:S. accepted i a p)"

  assumes chosen_topology:
    "\<And> i p. chosen' i p \<Longrightarrow> instance_topology_version' i \<le> Suc (prop_topology_version p)"

  assumes chosen_Suc: "\<And>i. some_chosen' (Suc i) \<Longrightarrow> some_chosen' i"

  shows "multiPaxosL lt le quorums_seq topology_version_increment prop_topology_version
  multi_promised promised_free promised_prev proposed accepted chosen'
  value_promised value_proposed' value_accepted"
using assms promised_free multi_promised promised_prev_accepted promised_prev_prev promised_prev_max
  accepts_proposed
apply unfold_locales
apply (fold defns)
proof -
  fix i p
  assume p: "proposed i p"
     
  from proposed_quorum [OF this]
  obtain S where quorum_S: "quorum' (prop_topology_version p) S"
    and promised_S: "\<And>a. a \<in> S \<Longrightarrow> (promised_free i a p \<or> (\<exists>j\<le>i. multi_promised j a p)) \<or> (\<exists>p1. promised_prev i a p p1)"
    and S_max: "\<And>a1 p1. \<lbrakk> a1 \<in> S; promised_prev i a1 p p1 \<rbrakk> \<Longrightarrow> value_proposed' i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2)"
    by auto

  from quorum_S
  show "\<exists>S. (rev (quorums_seq (values_lt_list' (SOME i. prop_topology_version p < length (quorums_seq (values_lt_list' i))))) ! prop_topology_version p) S \<and>
               (\<forall>a\<in>S. (promised_free i a p \<or> (\<exists>j\<le>i. multi_promised j a p)) \<or> (\<exists>p1. promised_prev i a p p1)) \<and> (\<forall>a1\<in>S. \<forall>p1. promised_prev i a1 p p1 \<longrightarrow> value_proposed' i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2))"
    by (unfold defns, intro exI [where x = S] conjI ballI allI impI S_max promised_S)

next
  fix i p
  assume c: "chosen' i p"
  from chosen_quorum [OF c]
  obtain S where quorum_S: "quorum' (prop_topology_version p) S"
    and accepted_S: "\<And>a. a \<in> S \<Longrightarrow> accepted i a p" 
    and nz: "S \<noteq> {}" by auto

  from quorum_S
  show "\<exists>S. S \<noteq> {} \<and> (rev (quorums_seq (values_lt_list' (SOME i. prop_topology_version p < length (quorums_seq (values_lt_list' i))))) ! prop_topology_version p) S \<and> (\<forall>a\<in>S. accepted i a p)"
    by (unfold defns, intro exI [where x = S] conjI ballI accepted_S nz)
qed (simp_all add: defns)

lemma (in multiPaxosL) multiPaxos_change_value_proposed:
  assumes proposed_eq: "\<And> i p. proposed i p \<Longrightarrow> value_proposed i p = value_proposed' i p"
  shows "multiPaxosL lt le quorums_seq topology_version_increment prop_topology_version
  multi_promised promised_free promised_prev proposed accepted
  chosen value_promised value_proposed' value_accepted"
proof -
  have p1: "\<And>i. some_chosen i = (EX p. chosen i p)" by (simp add: some_chosen_def)
  have p2: "value_chosen = (%i. THE v. EX p. chosen i p \<and> value_proposed' i p = v)" 
  proof -
    have i: "\<And>A B C. (A \<Longrightarrow> B = C) \<Longrightarrow> (A \<and> B) = (A \<and> C)"
            "\<And>x y z. x = y \<Longrightarrow> (x = z) = (y = z)" by auto

    show ?thesis
    proof (unfold value_chosen_def, intro ext i proposed_eq
        cong [OF refl, where f = The]
        cong [OF refl, where f = Ex])
      fix i p
      assume chosen: "chosen i p"
      from chosen_quorum [OF this]
      obtain a where "accepted i a p" by auto
      from accepts_proposed [OF this] show "proposed i p" .
    qed
  qed

  have p3: "\<And>i. values_lt_list i = map value_chosen (desc_lt i)" by (simp add: values_lt_list_def)
  have p4: "\<And>i. instance_topology_version i = topology_version (values_lt_list i)" by (simp add: instance_topology_version_def)
  have p5: "\<And>tv. quorum tv = rev (quorums_seq (values_lt_list (SOME i. tv < length (quorums_seq (values_lt_list i))))) ! tv"
    by (simp add: quorum_def)

  show ?thesis
  using accepts_proposed accepts_value chosen_Suc chosen_quorum
    chosen_topology multi_promised promised_free
    promised_prev_accepted promised_prev_max promised_prev_prev
    proposed_quorum proposed_topology  quorum_finite
    quorum_inter quorum_inter_Suc quorum_nonempty 
    quorums_seq_nonempty assms
  apply (intro multiPaxos_intro [OF p1 p2 p3 p4 p5])
    by (simp_all)
qed

lemma (in multiPaxosL) multiPaxos_add_choice:
  assumes quorum_S: "quorum (prop_topology_version p0) S"
  assumes accepted_S: "\<And>a. a \<in> S \<Longrightarrow> accepted i0 a p0"
  assumes nonempty_S: "S \<noteq> {}"
  assumes topo_version: "instance_topology_version i0 \<le> Suc (prop_topology_version p0)"
  assumes chosen_pred: "i0 > 0 \<Longrightarrow> some_chosen (i0 - 1)"

  defines chosen'_def: "chosen' == (%i p. (i, p) = (i0, p0) \<or> chosen i p)" 

  shows "multiPaxosL lt le quorums_seq topology_version_increment prop_topology_version
  multi_promised promised_free promised_prev proposed accepted chosen'
  value_promised value_proposed value_accepted"

proof -
  def some_chosen' == "(%i. EX p. chosen' i p)"
  def value_chosen' == "(%i. THE v. EX p. chosen' i p \<and> value_proposed i p = v)"
  def values_lt_list' == "(%i. map value_chosen' (desc_lt i))"
  def instance_topology_version' == "(%i. topology_version (values_lt_list' i))"
  def quorum' == "(%tv. rev (quorums_seq (values_lt_list' (SOME i. tv < length (quorums_seq (values_lt_list' i))))) ! tv)"

  have value_chosen_eq: "\<And>i. i < i0 \<Longrightarrow> value_chosen' i = value_chosen i"
    by (auto simp add: value_chosen_def value_chosen'_def chosen'_def)

  have values_lt_list_eq: "\<And>i. i \<le> i0 \<Longrightarrow> values_lt_list' i = values_lt_list i"
    by (unfold values_lt_list_def values_lt_list'_def, intro map_cong [OF refl], simp add: desc_lt_seq value_chosen_eq)

  hence instance_topology_version_eq: "\<And>i. i \<le> i0 \<Longrightarrow> instance_topology_version' i = instance_topology_version i"
    by (simp add: instance_topology_version'_def instance_topology_version_def)

  have values_lt_list_append: "\<And>i j. i \<le> j \<Longrightarrow> EX vs. values_lt_list j = vs @ values_lt_list i"
  proof -
    fix i j :: nat assume ij: "i \<le> j"
    show "?thesis i j"  by (unfold values_lt_list_def desc_lt_append [OF ij], auto)
  qed

  have values_lt_list'_append: "\<And>i j. i \<le> j \<Longrightarrow> EX vs. values_lt_list' j = vs @ values_lt_list' i"
  proof -
    fix i j :: nat assume ij: "i \<le> j"
    show "?thesis i j"  by (unfold values_lt_list'_def desc_lt_append [OF ij], auto)
  qed

  have quorum_eq: "\<And>tv. tv \<le> instance_topology_version i0 \<Longrightarrow> quorum' tv = quorum tv"
  apply (unfold quorum_topology_version quorum'_def)
  apply (intro take_mem_eq)
  proof -
    fix tv
    assume le: "tv \<le> instance_topology_version i0"

    have tv_lt_len: "tv < length (quorums_seq (values_lt_list' i0))"
    proof -
      note le
      also have "... = topology_version (values_lt_list i0)" by (simp add: instance_topology_version_def)
      also note topology_version_lt
      also have "length (quorums_seq (values_lt_list i0)) = length (quorums_seq (values_lt_list' i0))"
        by (intro cong [OF refl, where f = length]
                   cong [OF refl, where f = quorums_seq]
                   sym  [OF values_lt_list_eq], simp)
      finally show "tv < ..." .
    qed

    obtain vs where vs: "values_lt_list i0 = vs @ values_lt_list (LEAST i. tv < length (quorums_seq (values_lt_list' i)))"
     by (metis values_lt_list_append Least_le tv_lt_len)

    obtain vs' where vs': "values_lt_list' (SOME  i. tv < length (quorums_seq (values_lt_list' i)))
                   = vs' @ values_lt_list' (LEAST i. tv < length (quorums_seq (values_lt_list' i)))"
      by (metis values_lt_list'_append Least_le someI tv_lt_len)


    have least_eqI: "\<And>P Q (i_example :: nat). P i_example \<Longrightarrow> Q i_example \<Longrightarrow> (\<And>j. j \<le> i_example \<Longrightarrow> P j = Q j) \<Longrightarrow> Least P = Least Q"
      by (metis LeastI_ex Least_le le_antisym)

    from tv_lt_len values_lt_list_eq
    have least_eq: "(LEAST i. tv < length (quorums_seq (values_lt_list i))) = (LEAST i. tv < length (quorums_seq (values_lt_list' i)))"
      by (intro least_eqI, auto)

    have "take (Suc tv) (rev (quorums_seq       (values_lt_list' (SOME  i. tv < length (quorums_seq (values_lt_list' i))))))
        = take (Suc tv) (rev (quorums_seq (vs' @ values_lt_list' (LEAST i. tv < length (quorums_seq (values_lt_list' i))))))"
      by (simp add: vs')
    also have "... = take (Suc tv) (rev (quorums_seq (values_lt_list' (LEAST i. tv < length (quorums_seq (values_lt_list' i))))))"
      by (intro sym [OF take_quorums_seq_append] Suc_leI, metis LeastI tv_lt_len)
    also have "... = take (Suc tv) (rev (quorums_seq (values_lt_list (LEAST i. tv < length (quorums_seq (values_lt_list i))))))"
      by (unfold least_eq, intro cong [OF refl, where f = "take (Suc tv)"]
                 cong [OF refl, where f = rev]
                 cong [OF refl, where f = quorums_seq]
                 values_lt_list_eq Least_le tv_lt_len)
    also have "... = take (Suc tv) (rev (quorums_seq (vs @ values_lt_list (LEAST i. tv < length (quorums_seq (values_lt_list i))))))"
    proof (intro take_quorums_seq_append Suc_leI LeastI)
      note tv_lt_len
      also from values_lt_list_eq have "length (quorums_seq (values_lt_list' i0)) = length (quorums_seq (values_lt_list i0))" by auto
      finally show "tv < ..." .
    qed
    also have "... = take (Suc tv) (rev (quorums_seq (vs @ values_lt_list (LEAST i. tv < length (quorums_seq (values_lt_list' i))))))"
      by (simp add: least_eq)
    also have "... = take (Suc tv) (rev (quorums_seq (values_lt_list i0)))" by (simp add: vs)
    
    finally show "take (Suc tv) (rev (quorums_seq (values_lt_list' (SOME i. tv < length (quorums_seq (values_lt_list' i)))))) = take (Suc tv) (rev (quorums_seq (values_lt_list i0)))" .
  qed

  have defns: "\<And>i. some_chosen' i = (\<exists>p. chosen' i p)" 
    "value_chosen' = (\<lambda>i. THE v. \<exists>p. chosen' i p \<and> value_proposed i p = v)"
    "\<And>i. values_lt_list' i = map value_chosen' (desc_lt i)" 
    "\<And>i. instance_topology_version' i = topology_version (values_lt_list' i)" 
    "\<And>tv. quorum' tv = rev (quorums_seq (values_lt_list' (SOME i. tv < length (quorums_seq (values_lt_list' i))))) ! tv"
      by (simp_all  add: quorum'_def value_chosen'_def instance_topology_version'_def some_chosen'_def values_lt_list'_def)

  have va: "\<And>i p a. accepted i a p \<Longrightarrow> value_accepted i a p = value_proposed i p" by (intro accepts_value)

  have sc: "\<And>i. some_chosen' (Suc i) \<Longrightarrow> some_chosen' i"
  proof -
    fix i
    assume sc_Suc: "some_chosen' (Suc i)"
    then obtain p where "(Suc i, p) = (i0, p0) \<or> chosen (Suc i) p"
      by (auto simp add: some_chosen'_def chosen'_def)
      
    hence "some_chosen i"
    proof (elim disjE)
      assume "chosen (Suc i) p"
      with chosen_Suc show "some_chosen i" by (auto simp add: some_chosen_def)
    next
      assume ip: "(Suc i, p) = (i0, p0)" hence eq: "i = i0 - 1" by auto
      from ip show "some_chosen i" by (unfold eq, intro chosen_pred, auto)
    qed
    thus "some_chosen' i" by (auto simp add: some_chosen_def some_chosen'_def chosen'_def)
  qed

  {
    assume chosen_quorum: "\<And>i p. chosen i p \<Longrightarrow> \<exists>S. S \<noteq> {} \<and> quorum' (prop_topology_version p) S \<and> (\<forall>a\<in>S. accepted i a p)"
       and chosen_topology: "\<And>i p. chosen i p \<Longrightarrow> instance_topology_version' i \<le> Suc (prop_topology_version p)"
       and quorum_i0: "quorum' (prop_topology_version p0) S"
       and topology_i0: "instance_topology_version' i0 \<le> Suc (prop_topology_version p0)"
    
    assume "\<And>i p. proposed i p \<Longrightarrow> \<exists>S. quorum' (prop_topology_version p) S \<and>
               (\<forall>a\<in>S. (promised_free i a p \<or> (\<exists>j\<le>i. multi_promised j a p)) \<or> (\<exists>p1. promised_prev i a p p1)) \<and> (\<forall>a1\<in>S. \<forall>p1. promised_prev i a1 p p1 \<longrightarrow> value_proposed i p = value_promised i a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised_prev i a2 p p2 \<and> p1 \<prec> p2))"
           "\<And>i p. proposed i p \<Longrightarrow> \<forall>j<i. some_chosen' j \<Longrightarrow> prop_topology_version p \<le> instance_topology_version' i"
    hence ?thesis
    proof (intro multiPaxos_intro [OF defns _ _ va _ _ sc])
      fix i p
      assume c: "chosen' i p"
      from c chosen_quorum quorum_i0 nonempty_S accepted_S show "\<exists>S. S \<noteq> {} \<and> quorum' (prop_topology_version p) S \<and> (\<forall>a\<in>S. accepted i a p)" by (auto simp add: chosen'_def)
      from c chosen_topology topology_i0 show "instance_topology_version' i \<le> Suc (prop_topology_version p)" by (auto simp add: chosen'_def)
    qed
  }
  note fast_intro = this      

  have chosen'_proposed: "\<And>i p. chosen' i p \<Longrightarrow> proposed i p"
      and chosen'_chosen_lt: "\<And>i p. chosen' i p \<Longrightarrow> \<forall>j<i. some_chosen j"
  proof -
    fix i p
    assume chosen': "chosen' i p"

    from chosen' obtain a where "accepted i a p"
    proof (unfold chosen'_def, elim disjE)
      assume "chosen i p"
      from chosen_quorum [OF this]
      obtain a where "accepted i a p" by auto
      thus thesis by (intro that)
    next
      assume "(i, p) = (i0, p0)"
      with nonempty_S accepted_S obtain a where "accepted i a p" by auto
      thus thesis by (intro that)
    qed
    thus proposed: "proposed i p" by (intro accepts_proposed)

    from chosen' show all_some_chosen: "\<forall>j<i. some_chosen j"
    proof (unfold chosen'_def, intro allI impI, elim disjE)
      fix j
      assume "chosen i p" hence sc: "some_chosen i" by (auto simp add: some_chosen_def)
      assume ji: "j < i"
      from chosen_le [OF sc ji] show "some_chosen j" by (auto simp add: some_chosen_def)
    next
      fix j
      assume ip: "(i,p) = (i0,p0)" and ji: "j < i"
      from ji ip have i0: "0 < i0" by auto
      with ji ip have "j = i0 - 1 \<or> j < i0 - 1" by auto
      with chosen_pred [OF i0] show "some_chosen j"
      proof (elim disjE)
        assume "j < i0 - 1"
        from chosen_le [OF chosen_pred [OF i0] this] show ?thesis .
      qed simp
    qed
  qed

  have all_some_chosen: "\<forall>j<i0. some_chosen j"
    by (metis Suc_inject Suc_pred' chosen_le chosen_pred comm_monoid_diff_class.diff_cancel gr0_implies_Suc less_imp_diff_less less_trans_Suc not_less_iff_gr_or_eq)

  {
    from accepted_S nonempty_S obtain a where "accepted i0 a p0" by auto
    from proposed_topology [OF accepts_proposed [OF this] all_some_chosen]
    have "prop_topology_version p0 \<le> instance_topology_version i0" .
  }
  note prop_le = this

  show ?thesis
  proof (cases "some_chosen i0")
    case True

    have chosen'_unfolding: "chosen' i0 = (%p. p = p0 \<or> chosen i0 p)" by (simp add: chosen'_def)
    
    have paxos_i0: "paxosL lt le
      (%p S. quorum (prop_topology_version p) S \<and> prop_topology_version p \<le> instance_topology_version i0)
      (%p S. quorum (prop_topology_version p) S \<and> prop_topology_version p \<le> instance_topology_version i0)
      (%a p. promised_free i0 a p \<or> (EX j. j \<le> i0 \<and> multi_promised j a p))
      (promised_prev i0) (proposed i0) (accepted i0) (chosen' i0)
      (value_promised i0) (value_proposed i0) (value_accepted i0)"
    proof (unfold chosen'_unfolding, intro paxosL.paxos_add_chosen multi_instances True conjI prop_le)
      from quorum_S show "quorum (prop_topology_version p0) S".
      from accepted_S show "\<And>a. a \<in> S \<Longrightarrow> accepted i0 a p0" .

      fix SP SL p1
      assume "quorum (prop_topology_version p1) SP \<and> prop_topology_version p1 \<le> instance_topology_version i0"
             "quorum (prop_topology_version p0) SL \<and> prop_topology_version p0 \<le> instance_topology_version i0"
      hence qSP: "quorum (prop_topology_version p1) SP" and qSL: "quorum (prop_topology_version p0) SL"
        and p1: "prop_topology_version p1 \<le> instance_topology_version i0" by simp_all

      assume proposed: "proposed i0 p1" and p01: "p0 \<prec> p1"
      from p01 have ptv01: "prop_topology_version p0 \<le> prop_topology_version p1" by (intro prop_topology_version_mono, auto)

      from ptv01 prop_le p1 topo_version
      have "prop_topology_version p1 = prop_topology_version p0 \<or> prop_topology_version p1 = Suc (prop_topology_version p0)" by auto
      thus "SP \<inter> SL \<noteq> {}"
      proof (elim disjE)
        assume eq: "prop_topology_version p1 = prop_topology_version p0"
        show ?thesis
        proof (intro quorum_inter)
          from qSP show "quorum (prop_topology_version p0) SP" by (simp add: eq)
          from qSL show "quorum (prop_topology_version p0) SL" .

          have "quorum (prop_topology_version p0) \<in> set (rev (quorums_seq (values_lt_list i0)))"
          proof (unfold quorum_topology_version [OF prop_le], intro nth_mem)
            note prop_le
            also have "instance_topology_version i0 < length (quorums_seq (values_lt_list i0))"
              by (unfold instance_topology_version_def, intro topology_version_lt)
            finally show "prop_topology_version p0 < length (rev (quorums_seq (values_lt_list i0)))" by simp
          qed
          thus "quorum (prop_topology_version p0) \<in> set (quorums_seq (values_lt_list i0))" by simp
        qed
      next
        assume eq: "prop_topology_version p1 = Suc (prop_topology_version p0)"
        show "SP \<inter> SL \<noteq> {}"
        proof (intro quorum_inter_Suc)
          have "quorum (prop_topology_version p1) = rev (quorums_seq (values_lt_list i0)) ! prop_topology_version p1"
            by (intro quorum_topology_version p1)
          also have "... = quorums_seq (values_lt_list i0) ! (length (quorums_seq (values_lt_list i0)) - Suc (prop_topology_version p1))"
          proof (intro rev_nth)
            note p1
            also have "instance_topology_version i0 < length (quorums_seq (values_lt_list i0))"
              by (unfold instance_topology_version_def, intro topology_version_lt)
            finally show "prop_topology_version p1 < ..." .
          qed
          finally have "quorum (prop_topology_version p1) = ..." .
          with qSP show "(quorums_seq (values_lt_list i0) ! (length (quorums_seq (values_lt_list i0)) - Suc (prop_topology_version p1))) SP" by simp

          have "Suc (length (quorums_seq (values_lt_list i0)) - Suc (prop_topology_version p1)) = (length (quorums_seq (values_lt_list i0)) - (prop_topology_version p1))"
          proof (intro Suc_diff_Suc)
            note p1
            also have "instance_topology_version i0 < length (quorums_seq (values_lt_list i0))"
              by (unfold instance_topology_version_def, intro topology_version_lt)
            finally show "prop_topology_version p1 < ..." .
          qed
          also have "... < length (quorums_seq (values_lt_list i0))"
          proof (intro diff_less)
            from eq show "0 < prop_topology_version p1" by simp
            also note p1
            also have "instance_topology_version i0 < length (quorums_seq (values_lt_list i0))"
              by (unfold instance_topology_version_def, intro topology_version_lt)
            finally show "0 < ..." .
          qed
          finally show "Suc (length (quorums_seq (values_lt_list i0)) - Suc (prop_topology_version p1)) < length (quorums_seq (values_lt_list i0))" .

          have "length (quorums_seq (values_lt_list i0)) - Suc (prop_topology_version p0)
            = length (quorums_seq (values_lt_list i0)) - prop_topology_version p1" by (simp add: eq)
          also have "... = Suc (length (quorums_seq (values_lt_list i0)) - Suc (prop_topology_version p1))"
          proof (intro sym [OF Suc_diff_Suc])
            note p1
            also have "instance_topology_version i0 < length (quorums_seq (values_lt_list i0))"
              by (unfold instance_topology_version_def, intro topology_version_lt)
            finally show "prop_topology_version p1 < ..." .
          qed
          finally have ix_eq: "length (quorums_seq (values_lt_list i0)) - Suc (prop_topology_version p0) = ..." .

          have "quorum (prop_topology_version p0) = rev (quorums_seq (values_lt_list i0)) ! prop_topology_version p0"
            by (intro quorum_topology_version prop_le)
          also have "... = quorums_seq (values_lt_list i0) ! (length (quorums_seq (values_lt_list i0)) - Suc (prop_topology_version p0))"
          proof (intro rev_nth)
            note prop_le
            also have "instance_topology_version i0 < length (quorums_seq (values_lt_list i0))"
              by (unfold instance_topology_version_def, intro topology_version_lt)
            finally show "prop_topology_version p0 < ..." .
          qed
          finally have "quorum (prop_topology_version p0) = ..." .
          with qSL ix_eq
          show "(quorums_seq (values_lt_list i0) ! Suc (length (quorums_seq (values_lt_list i0)) - Suc (prop_topology_version p1))) SL" by simp
        qed
      qed
    qed

  
    from True
    have some_chosen_eq: "some_chosen' = some_chosen"
      by (auto simp add: some_chosen'_def some_chosen_def chosen'_def)

    have value_chosen_eq: "value_chosen' = value_chosen"
    proof (intro ext)
      fix i
      from True obtain p0' where chosen_i0: "chosen i0 p0'" by (auto simp add: some_chosen_def)

      show "value_chosen' i = value_chosen i"
      proof (cases "i = i0")
        case True

        have "value_chosen' i0 = value_proposed i0 p0'"
        proof (unfold value_chosen'_def chosen'_def, rule theI2)
          show "\<exists>p. ((i0, p) = (i0, p0) \<or> chosen i0 p) \<and> value_proposed i0 p = value_proposed i0 p0" by auto
          fix v
          assume "\<exists>p. ((i0, p) = (i0, p0) \<or> chosen i0 p) \<and> value_proposed i0 p = v"
          then obtain p where chosen: "(i0, p) = (i0, p0) \<or> chosen i0 p" and p: "v = value_proposed i0 p" by auto

          note p
          also from chosen chosen_i0 have "value_proposed i0 p = value_proposed i0 p0'"
            by (intro paxosL.paxos_consistent [OF paxos_i0], auto simp add: chosen'_def)
          finally show "v = value_proposed i0 p0'" by auto

          note p
          also from chosen chosen_i0 have "value_proposed i0 p = value_proposed i0 p0"
            by (intro paxosL.paxos_consistent [OF paxos_i0], auto simp add: chosen'_def)
          finally show "v = value_proposed i0 p0" by auto
        qed
        also have "... = value_chosen i0" by (intro sym [OF multiPaxos_the_value] chosen_i0)
        finally show "value_chosen' i = value_chosen i" by (simp add: True)
      qed (auto simp add: value_chosen'_def value_chosen_def chosen'_def)
    qed

    have values_lt_list_eq: "values_lt_list' = values_lt_list"
      by (simp add: values_lt_list'_def values_lt_list_def value_chosen_eq)

    have instance_topology_version_eq: "instance_topology_version' = instance_topology_version"
      and quorum_eq: "quorum' = quorum"
      by (simp_all add: instance_topology_version'_def instance_topology_version_def values_lt_list_eq quorum'_def quorum_def)

    from topo_version quorum_S chosen_quorum chosen_topology proposed_topology proposed_quorum
    show ?thesis by (intro fast_intro, unfold instance_topology_version_eq quorum_eq some_chosen_eq, auto)

  next
    case False

    from False chosen_le have some_chosen_eq: "some_chosen = (%i. i < i0)"
    apply (intro ext iffI)
    apply (metis nat_neq_iff)
      by (metis Suc_inject Suc_pred' chosen_le chosen_pred diff_self_eq_0 gr0_implies_Suc less_imp_diff_less less_trans_Suc not_less_iff_gr_or_eq)

    have "\<And>i p. chosen i p \<Longrightarrow> some_chosen i" by (auto simp add: some_chosen_def)
    hence chosen_lt: "\<And>i p. chosen i p \<Longrightarrow> i < i0" by (simp add: some_chosen_eq)

    have some_chosen'_eq: "some_chosen' = (%i. i \<le> i0)"
    proof (intro ext)
      fix i
      from less_linear [of i i0]
      show "some_chosen' i = (i \<le> i0)"
      proof (elim disjE) (*, auto simp add: some_chosen'_def chosen'_def)*)
        assume ii0: "i < i0"
        with some_chosen_eq have "some_chosen i" by auto
        with ii0 show ?thesis
          by (auto simp add: some_chosen'_def chosen'_def some_chosen_def)
      next
        assume i0i: "i0 < i"
        hence "i \<noteq> i0" "\<not> some_chosen i" by (simp_all add: some_chosen_eq)
        with i0i show ?thesis
          by (auto simp add: some_chosen'_def chosen'_def some_chosen_def)
      qed (auto simp add: some_chosen'_def chosen'_def some_chosen_def)
    qed

    have all_j_i_lt: "\<And>i. \<forall>j<i. some_chosen' j \<Longrightarrow> i \<le> Suc i0"
    apply (unfold some_chosen'_eq)
      by (metis Suc_n_not_le_n not_le)

    have value_chosen_i0: "value_chosen' i0 = value_proposed i0 p0"
    proof (unfold value_chosen'_def, rule theI2)
      show "\<exists>p. chosen' i0 p \<and> value_proposed i0 p = value_proposed i0 p0"
        by (auto simp add: chosen'_def)

      fix v
      assume "\<exists>p. chosen' i0 p \<and> value_proposed i0 p = v"
      then obtain p where c: "chosen' i0 p" and v: "value_proposed i0 p = v" by auto

      from c False have "p0 = p" by (auto simp add: chosen'_def some_chosen_def)
      with v show "v = value_proposed i0 p0" "v = value_proposed i0 p0" by auto
    qed

    show ?thesis
    proof (intro fast_intro)
      have "quorum' (prop_topology_version p0) S = quorum (prop_topology_version p0) S"
        by (intro cong [OF quorum_eq] refl prop_le)
      also note quorum_S
      finally show "quorum' (prop_topology_version p0) S" .

      have "instance_topology_version' i0 = instance_topology_version i0"
        by (auto simp add: instance_topology_version_eq)
      also note topo_version
      finally show "instance_topology_version' i0 \<le> Suc (prop_topology_version p0)".

    next
      fix i p
      assume c: "chosen i p"
      note ii0 = chosen_lt [OF c]

      from ii0
      have "instance_topology_version' i = instance_topology_version i"
        by (auto simp add: instance_topology_version_eq)
      also note chosen_topology [OF c]
      finally show "instance_topology_version' i \<le> Suc (prop_topology_version p)" .

      have "quorum' (prop_topology_version p) = quorum (prop_topology_version p)"
      proof (intro quorum_eq)
        from ii0 have all_j_i: "\<forall>j<i. some_chosen j" by (unfold some_chosen_eq, auto)
  
        from ii0 desc_lt_append
        have "map value_chosen (desc_lt i0) = map value_chosen (map (\<lambda>j. j + i) (desc_lt (i0 - i)) @ desc_lt i)"
          by (intro cong [OF refl desc_lt_append, where f = "map value_chosen"], simp)
        hence map_eq: "map value_chosen (desc_lt i0) = (map value_chosen (map (\<lambda>j. j + i) (desc_lt (i0 - i)))) @ (map value_chosen (desc_lt i))"
          by simp

        from chosen_quorum [OF c]
        obtain a where accepted: "accepted i a p" by auto
        note proposed_topology [OF accepts_proposed [OF this] all_j_i]
        also have "instance_topology_version i \<le> instance_topology_version i0"
          by (unfold instance_topology_version_def values_lt_list_def map_eq, intro topology_version_mono)
        finally show "prop_topology_version p \<le> instance_topology_version i0" .
      qed

      with chosen_quorum [OF c]
      show "\<exists>S. S \<noteq> {} \<and> quorum' (prop_topology_version p) S \<and> (\<forall>a\<in>S. accepted i a p)" by simp

    next
      fix i p
      assume proposed: "proposed i p" and all_j_i': "\<forall>j<i. some_chosen' j"
     
      from all_j_i_lt [OF all_j_i'] have ii0: "i \<le> Suc i0" .

      from ii0 have i_options3: "i < i0 \<or> i = i0 \<or> i = Suc i0" by auto
      from ii0 have i_options2: "i \<le> i0 \<or> i = Suc i0" by auto

      from i_options2
      show "prop_topology_version p \<le> instance_topology_version' i"
      proof (elim disjE)
        assume ii0: "i \<le> i0"
        with all_some_chosen have all_j_i: "\<forall>j<i. some_chosen j" by auto
        note proposed_topology [OF proposed all_j_i]
        also from ii0 have "instance_topology_version i = instance_topology_version' i"
          by (intro sym [OF instance_topology_version_eq], simp)
        finally show "prop_topology_version p \<le> instance_topology_version' i" .
      next
        assume ii0: "i = Suc i0"
        have "instance_topology_version' i = instance_topology_version' (Suc i0)" by (simp add: ii0)
        also have "... = (SOME x. False)"
        proof (unfold instance_topology_version'_def values_lt_list'_def, simp add: Let_def)
