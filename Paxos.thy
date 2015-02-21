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

locale quorateL = 
  fixes quorate_proposer :: "'acceptor set \<Rightarrow> bool"
  fixes quorate_learner  :: "'acceptor set \<Rightarrow> bool"

  assumes quorate_inter:
    "\<And> SP SL. \<lbrakk> quorate_proposer SP; quorate_learner SL \<rbrakk> \<Longrightarrow> SP \<inter> SL \<noteq> {}"
  assumes quorate_finite: "\<And> SP. quorate_proposer SP \<Longrightarrow> finite SP"

  assumes quorum_exists: "EX SP. quorate_proposer SP"

locale paxosL = propNoL + quorateL +

  fixes promised :: "'acceptor \<Rightarrow> 'pid \<Rightarrow> 'pid option \<Rightarrow> bool"
  fixes proposed :: "'pid \<Rightarrow> bool"
  fixes accepted :: "'acceptor \<Rightarrow> 'pid \<Rightarrow> bool"
  fixes chosen :: "'pid \<Rightarrow> bool"
  fixes value_promised :: "'acceptor \<Rightarrow> 'pid \<Rightarrow> 'value"
  fixes value_proposed :: "'pid \<Rightarrow> 'value"
  fixes value_accepted :: "'acceptor \<Rightarrow> 'pid \<Rightarrow> 'value"

  assumes chosen_quorum:
    "\<And> p . chosen p \<Longrightarrow> EX S. quorate_learner S \<and> (ALL a:S. accepted a p)"
  assumes proposed_quorum:
    "\<And> p . proposed p \<Longrightarrow> EX S. quorate_proposer S
      \<and> (ALL a:S. EX mp. promised a p mp)
      \<and> (ALL a1:S. ALL p1. promised a1 p (Some p1)
          \<longrightarrow> value_proposed p = value_promised a1 p
          \<or> (EX a2:S. EX p2. promised a2 p (Some p2) \<and> p1 \<prec> p2))"
  assumes accepts_proposed:
    "\<And> p a. accepted a p \<Longrightarrow> proposed p"
  assumes accepts_value:
    "\<And> p a. accepted a p \<Longrightarrow> value_accepted a p = value_proposed p"
  assumes promised_Some_accepted:
    "\<And> a p0 p1. promised a p0 (Some p1) \<Longrightarrow> accepted a p1 \<and> p1 \<prec> p0"
  assumes promised_Some:
    "\<And> a p0 p1 p2. \<lbrakk> promised a p0 (Some p1); accepted a p2; p2 \<prec> p0 \<rbrakk>
      \<Longrightarrow> ((p1 = p2 \<and> value_accepted a p1 = value_promised a p0) \<or> p2 \<prec> p1)"
  assumes promised_None:
    "\<And> a p0 p1. \<lbrakk> promised a p0 None; accepted a p1 \<rbrakk> \<Longrightarrow> p0 \<preceq> p1"

lemma (in paxosL) promised_some_none:
  assumes "promised a p0 (Some p1)" "promised a p0 None"
  shows P
proof -
  have "promised a p0 (Some p1) \<longrightarrow> \<not> promised a p0 None"
    by (metis promised_None promised_Some_accepted propNo_leE propNo_lt_not_ge_E)
  with assms show P by simp
qed

lemma (in paxosL) promised_fun:
  assumes "promised a p0 mp1" "promised a p0 mp2"
  shows "mp1 = mp2"
  apply (cases mp1)
  apply (cases mp2)
  apply (simp)
  apply (metis assms promised_some_none)
  apply (cases mp2)
  apply (metis assms promised_some_none)
  by (metis assms promised_Some promised_Some_accepted propNo_lt_not_ge_E)

lemma (in paxosL)
  assumes "quorate_proposer S"
  shows paxos_max_proposer: "(ALL a1:S. ALL mp. promised a1 p mp \<longrightarrow> mp = None) 
 \<or> (EX a1:S. EX p1. promised a1 p (Some p1)
         \<and> (ALL a3:S. ALL p3. promised a3 p (Some p3) \<longrightarrow> p3 \<preceq> p1))"
  (is "?P1 S \<or> ?P2 S")
proof -
  from assms quorate_finite
  have "finite S" by simp
  thus ?thesis
  proof (induct S rule: finite_induct)
    case empty thus ?case by simp
  next
    case (insert a S')
  
    show ?case
    proof (cases "EX mp. promised a p mp")
      case False
      from insert.hyps
      show ?thesis
      proof (elim disjE)
        assume hyp1: "?P1 S'"
        show ?thesis
          by (intro disjI1 ballI allI impI, metis False hyp1 insert_iff)
      next
        assume hyp2: "?P2 S'"
        then obtain a1 p1 where a1S: "a1 \<in> S'" and p: "promised a1 p (Some p1)"
          and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S'; promised a3 p (Some p3) \<rbrakk> \<Longrightarrow> p3 \<preceq> p1"
          by auto
        
        show ?thesis
        proof (intro disjI2 bexI exI conjI ballI allI impI)
          from p show "promised a1 p (Some p1)" .
          from a1S show "a1 \<in> insert a S'" by simp
          fix a3 p3
          assume "a3 \<in> insert a S'" and "promised a3 p (Some p3)"
          thus "p3 \<preceq> p1" by (metis False insert_iff p1_max)
        qed
      qed
    next
      case True
      then obtain mp where mp: "promised a p mp" by auto
      show ?thesis
      proof (cases mp)
        case None
        from insert.hyps
        show ?thesis
        proof (elim disjE)
          assume hyp1: "?P1 S'"
          show ?thesis 
          proof (intro disjI1 ballI allI impI)
            fix a1 mp'
            assume "a1 \<in> insert a S'" and p: "promised a1 p mp'"
            thus "mp' = None"
              by (metis None hyp1 insert_iff local.mp promised_fun)
          qed
        next
          assume hyp2: "?P2 S'"
          then obtain a1 p1 where a1S: "a1 \<in> S'" and p: "promised a1 p (Some p1)"
            and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S'; promised a3 p (Some p3) \<rbrakk> \<Longrightarrow> p3 \<preceq> p1"
            by auto
          show ?thesis
          proof (intro disjI2 bexI exI conjI impI ballI allI)
            from p show "promised a1 p (Some p1)" .
            from a1S show "a1 \<in> insert a S'" by simp
            fix a3 p3 assume "a3 \<in> insert a S'" and p: "promised a3 p (Some p3)"
            thus "p3 \<preceq> p1" by (metis None insert_iff local.mp p1_max promised_some_none)
          qed
        qed
      next
        case (Some p0)
        
        from insert.hyps
        have "?P2 (insert a S')"
        proof (elim disjE)
          assume "?P1 S'"
          hence none_proposed: "\<And> a1 mp. \<lbrakk> a1 \<in> S'; promised a1 p mp \<rbrakk> \<Longrightarrow> mp = None" by simp
          show ?thesis
          proof (intro bexI exI conjI impI ballI allI)
            show "a \<in> insert a S'" by simp
            from mp Some show "promised a p (Some p0)" by simp
            fix a3 p3
            assume "a3 \<in> insert a S'" and p: "promised a3 p (Some p3)"
            with none_proposed have a3: "a3 = a" by auto
            have "Some p0 = Some p3" by (metis Some a3 local.mp p promised_fun)
            thus "p3 \<preceq> p0" by simp
          qed
        next
          assume "?P2 S'"
          then obtain a1 p1 where a1S: "a1 \<in> S'" and p: "promised a1 p (Some p1)"
            and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S'; promised a3 p (Some p3) \<rbrakk> \<Longrightarrow> p3 \<preceq> p1" by auto
          have le: "p0 \<preceq> p1 \<Longrightarrow> ?thesis"
          proof (intro bexI exI conjI ballI allI impI)
            assume p10: "p0 \<preceq> p1"
            hence p10_cases: "p0 \<prec> p1 \<or> p0 = p1" by simp
            from p show "promised a1 p (Some p1)" .
            from a1S show "a1 \<in> insert a S'" by simp
            fix a3 p3
            assume "a3 \<in> insert a S'"
              and p3: "promised a3 p (Some p3)"
            hence "a3 = a \<or> a3 \<in> S'" by simp
            from this p10_cases show "p3 \<preceq> p1"
            apply (elim disjE)
            apply (metis Some p10 local.mp option.sel p3 promised_fun)
            apply (metis Some le_lt_eq local.mp option.sel p3 promised_fun)
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
              from mp Some show "promised a p (Some p0)" by simp
              show "a \<in> insert a S'" by simp
              fix a3 p3
              assume "a3 \<in> insert a S'"
                and p3: "promised a3 p (Some p3)"
              hence "a3 = a \<or> a3 \<in> S'" by simp
              thus "p3 \<preceq> p0"
              by (elim disjE,
                  metis Some le_lt_eq local.mp option.sel p3 promised_fun,
                  metis le_lt_eq p1_max p1p p3 propNo_trans_le_le)
            qed
          qed
        qed
  
        thus ?thesis by simp
      qed
    qed
  qed
qed

lemma (in paxosL) p2c:
  assumes proposed_p0: "proposed p0"
  obtains S where "quorate_proposer S"
    and "(ALL a1 : S. ALL p1. p1 \<prec> p0 \<longrightarrow> \<not> accepted a1 p1)
    \<or> (EX a1 : S. EX p1. accepted a1 p1
        \<and> value_proposed p0 = value_accepted a1 p1
        \<and> p1 \<prec> p0
        \<and> (ALL a2 : S. ALL p2. (accepted a2 p2 \<and> p2 \<prec> p0) \<longrightarrow> p2 \<preceq> p1))"
proof -
  from proposed_quorum [OF proposed_p0]
  obtain S where quorate_S: "quorate_proposer S"
    and S_promised: "\<And> a1. a1 \<in> S \<Longrightarrow> \<exists>mp1. promised a1 p0 mp1"
    and S_value: "\<And>a1 p1. \<lbrakk> a1 \<in> S; promised a1 p0 (Some p1) \<rbrakk> \<Longrightarrow> value_proposed p0 = value_promised a1 p0 \<or> (\<exists>a2\<in>S. \<exists>p2. promised a2 p0 (Some p2) \<and> p1 \<prec> p2)"
    by auto
  show thesis
  proof (intro that)
    from quorate_S show "quorate_proposer S" .
    show "(ALL a1 : S. ALL p1. p1 \<prec> p0 \<longrightarrow> \<not> accepted a1 p1)
        \<or> (EX a1 : S. EX p1. accepted a1 p1
            \<and> value_proposed p0 = value_accepted a1 p1
            \<and> p1 \<prec> p0
            \<and> (ALL a2 : S. ALL p2. (accepted a2 p2 \<and> p2 \<prec> p0) \<longrightarrow> p2 \<preceq> p1))"
    (is "?ALLFRESH \<or> ?EXISTSMAX")
    proof (cases "ALL a1:S. promised a1 p0 None")
      case True
      show ?thesis
        by (metis True promised_None propNo_irreflexive propNo_trans_lt_le)
    next
      case False
      then obtain a2 where a2S: "a2 \<in> S" and not_None: "\<not> promised a2 p0 None" by auto
      from S_promised a2S obtain mp2 where "promised a2 p0 mp2" by auto
      with not_None obtain p2 where p2: "promised a2 p0 (Some p2)"
        by (cases mp2, auto)
    
      from paxos_max_proposer [OF quorate_S, where p = p0]
      obtain a1 p1
        where a1S: "a1 \<in> S"
        and p1: "promised a1 p0 (Some p1)"
        and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S; promised a3 p0 (Some p3) \<rbrakk> \<Longrightarrow> p3 \<preceq> p1"
          by (metis a2S option.distinct(2) p2)
  
      from p1 promised_Some_accepted have lt10: "p1 \<prec> p0" by auto
  
      show ?thesis
      proof (intro exI conjI disjI2 bexI ballI allI impI)
        from p1 promised_Some_accepted show acc1: "accepted a1 p1" by simp
        from a1S show "a1 \<in> S" .

        from S_value [OF a1S p1]
        show "value_proposed p0 = value_accepted a1 p1"
          by (metis acc1 lt10 p1 p1_max promised_Some propNo_leE propNo_lt_not_ge_E)

        from lt10 show "p1 \<prec> p0" .
  
        fix a3 p3 assume a3S: "a3 \<in> S" and "accepted a3 p3 \<and> p3 \<prec> p0"
        hence acc3: "accepted a3 p3" and lt30: "p3 \<prec> p0" by auto
  
        from a3S S_promised obtain mp3 where mp3: "promised a3 p0 mp3" by auto
        
        show "p3 \<preceq> p1"
        proof (cases mp3)
          case None thus ?thesis by (metis acc3 lt30 mp3 promised_None propNo_leE propNo_lt_not_ge_E)
        next
          case Some thus ?thesis by (metis acc3 lt30 a3S le_lt_eq mp3 p1_max promised_Some propNo_trans_lt_le)
        qed
      qed
    qed
  qed
qed

lemma (in paxosL) p2b: 
  assumes chosen: "chosen p0"
  shows "\<And>p1. \<lbrakk> proposed p1; p0 \<preceq> p1 \<rbrakk> \<Longrightarrow> value_proposed p0 = value_proposed p1"
proof -
  from chosen_quorum [OF chosen] obtain SL
    where SC_quorate: "quorate_learner SL"
    and SC_accepts: "\<And>a. \<lbrakk> a \<in> SL \<rbrakk> \<Longrightarrow> accepted a p0" by auto

  fix p1_base
  assume "proposed p1_base" "p0 \<preceq> p1_base" thus "?thesis p1_base"
  proof (induct p1_base rule: wf_induct [OF wf])
    fix p1
    assume proposed: "proposed p1" and p01: "p0 \<preceq> p1"
    assume "\<forall>p2. (p2, p1) \<in> {(p,q). p \<prec> q} \<longrightarrow> proposed p2 \<longrightarrow> p0 \<preceq> p2 \<longrightarrow> value_proposed p0 = value_proposed p2"
      hence
      hyp: "\<And>p2. \<lbrakk> p2 \<prec> p1; proposed p2; p0 \<preceq> p2 \<rbrakk> \<Longrightarrow> value_proposed p0 = value_proposed p2" by auto

    from p01
    show "value_proposed p0 = value_proposed p1"
    proof (elim propNo_leE)
      assume lt01: "p0 \<prec> p1"
      show ?thesis
      proof -

        from p2c [OF proposed] obtain SP where SP_quorate: "quorate_proposer SP"
          and S_mess: "((\<forall>a1\<in>SP. \<forall>p1a. p1a \<prec> p1 \<longrightarrow> \<not> accepted a1 p1a)
          \<or> (\<exists>a1\<in>SP. \<exists>p1a. accepted a1 p1a \<and> value_proposed p1 = value_accepted a1 p1a \<and> p1a \<prec> p1
              \<and> (\<forall>a2\<in>SP. \<forall>p2. accepted a2 p2 \<and> p2 \<prec> p1 \<longrightarrow> p2 \<preceq> p1a)))"
          (is "?P1 \<or> ?P2") by auto
  
        from SP_quorate SC_quorate quorate_inter
        obtain a where aSP: "a \<in> SP" and aSC: "a \<in> SL" by auto

        from S_mess
        show "value_proposed p0 = value_proposed p1"
        proof (elim disjE)
          assume "?P1"
          thus ?thesis
            by (metis SC_accepts aSC aSP lt01)
        next
          assume "?P2"
          thus ?thesis
            by (metis SC_accepts aSC aSP accepts_proposed accepts_value hyp lt01)
        qed
      qed
    qed simp
  qed
qed

lemma (in paxosL)
  assumes "chosen p0" and "accepted a1 p1" and "p0 \<preceq> p1"
  shows p2a: "value_proposed p0 = value_proposed p1"
  using assms by (intro p2b accepts_proposed)

lemma (in paxosL)
  assumes chosen0: "chosen p0"
  assumes chosen1: "chosen p1"
  assumes p01: "p0 \<preceq> p1"
  shows p2: "value_proposed p0 = value_proposed p1"
  by (metis assms Int_empty_right chosen_quorum equals0I p2a quorate_inter quorum_exists)

theorem (in paxosL)
  assumes chosen0: "chosen p0"
  assumes chosen1: "chosen p1"
  shows paxos_consistent: "value_proposed p0 = value_proposed p1"
  by (metis assms le_lt_eq p2 propNo_cases)

lemma paxos_empty:
  assumes propNoL: "propNoL lt le"
  assumes quorateL: "quorateL quorum_proposer quorum_learner"
  assumes no_promise: "\<And> a p mp. \<not>promised a p mp"
  assumes no_proposed: "\<And> p. \<not>proposed p"
  assumes no_accepted: "\<And> a p. \<not>accepted a p"
  assumes no_chosen: "\<And> p. \<not>chosen p"

  shows "paxosL lt le quorum_proposer quorum_learner promised proposed accepted chosen value_promised value_proposed value_accepted"
using assms by (auto simp add: paxosL_def paxosL_axioms_def)

lemma (in paxosL) paxos_propNo [simp]: "propNoL lt le"
using wf trans total by (auto simp add: propNoL_def)

lemma (in paxosL) paxos_quorate [simp]: "quorateL quorate_proposer quorate_learner"
using quorate_finite quorate_inter quorum_exists by (auto simp add: quorateL_def)

lemma (in paxosL) paxos_add_proposal_free:
  assumes quorate_S: "quorate_proposer S"
  assumes promised_S: "\<And>a. a \<in> S \<Longrightarrow> promised a p0 None"
  shows "paxosL lt le quorate_proposer quorate_learner promised (%p. p = p0 \<or> proposed p) accepted chosen value_promised value_proposed value_accepted"
(* the proposer only needs to know about 'promised' messages to send a 'proposed' message *)
using chosen_quorum accepts_proposed promised_Some_accepted promised_None promised_Some accepts_value
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)

  from proposed_quorum
  show "\<forall>p. p = p0 \<or> proposed p \<longrightarrow> (\<exists>S. quorate_proposer S \<and> (\<forall>a\<in>S. \<exists>mp. promised a p mp) \<and> (\<forall>a1\<in>S. \<forall>p1. promised a1 p (Some p1) \<longrightarrow> value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised a2 p (Some p2) \<and> p1 \<prec> p2)))"
  proof (intro allI impI, elim disjE)
    fix p assume pp0: "p = p0"
    show "\<exists>S. quorate_proposer S \<and> (\<forall>a\<in>S. \<exists>mp. promised a p mp) \<and> (\<forall>a1\<in>S. \<forall>p1. promised a1 p (Some p1) \<longrightarrow> value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised a2 p (Some p2) \<and> p1 \<prec> p2))"
    proof (intro exI [where x = S] conjI ballI allI impI)
      from quorate_S show "quorate_proposer S" .
      fix a1 assume a1S: "a1 \<in> S"
      with promised_S pp0 show "EX mp. promised a1 p mp" by auto

      fix p1 assume p1: "promised a1 p (Some p1)"
      have "Some p1 = None"
      proof (intro promised_fun)
        from p1 show "promised a1 p (Some p1)" .
        from promised_S a1S pp0 show "promised a1 p None" by simp
      qed
      thus "value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised a2 p (Some p2) \<and> p1 \<prec> p2)" by simp
    qed
  qed simp
qed simp_all


lemma (in paxosL) paxos_add_proposal_constrained:
  assumes quorate_S: "quorate_proposer S"
  assumes promised_S: "\<And>a. a \<in> S \<Longrightarrow> EX mp. promised a p0 mp"
  assumes promised_S_value: "\<And>a p1. a \<in> S \<Longrightarrow> promised a p0 (Some p1) \<Longrightarrow> value_proposed p0 = value_promised a p0 \<or> (\<exists>a2\<in>S. \<exists>p2. promised a2 p0 (Some p2) \<and> p1 \<prec> p2)"
  shows "paxosL lt le quorate_proposer quorate_learner promised (%p. p = p0 \<or> proposed p) accepted chosen value_promised value_proposed value_accepted"
(* the Proposer only needs to know about promised messages (and 'value') to send a 'proposed' message *)
using chosen_quorum accepts_proposed promised_Some_accepted promised_None promised_Some accepts_value
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)
  from proposed_quorum
  show "\<forall>p. p = p0 \<or> proposed p \<longrightarrow> (\<exists>S. quorate_proposer S \<and> (\<forall>a\<in>S. \<exists>mp. promised a p mp) \<and> (\<forall>a1\<in>S. \<forall>p1. promised a1 p (Some p1) \<longrightarrow> value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised a2 p (Some p2) \<and> p1 \<prec> p2)))"
  proof (intro allI impI, elim disjE)
    fix p assume pp0: "p = p0"
    show "\<exists>S. quorate_proposer S \<and> (\<forall>a\<in>S. \<exists>mp. promised a p mp) \<and> (\<forall>a1\<in>S. \<forall>p1. promised a1 p (Some p1) \<longrightarrow> value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised a2 p (Some p2) \<and> p1 \<prec> p2))"
    proof (intro exI [where x = S] conjI ballI allI impI)
      from quorate_S show "quorate_proposer S" .
      fix a1 assume a1S: "a1 \<in> S"
      with promised_S pp0 show "EX mp. promised a1 p mp" by simp

      fix p1 assume p1: "promised a1 p (Some p1)"
      with pp0 have "promised a1 p0 (Some p1)" by simp
      from promised_S_value [OF a1S this]
      show "value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised a2 p (Some p2) \<and> p1 \<prec> p2)" by (simp add: pp0)
    qed
  qed simp
qed simp_all

lemma (in paxosL) paxos_add_choice:
  assumes quorate_S: "quorate_learner S"
  assumes accepted_S: "\<And>a. a \<in> S \<Longrightarrow> accepted a p0"
  shows "paxosL lt le quorate_proposer quorate_learner promised proposed accepted (%p. p = p0 \<or> chosen p) value_promised value_proposed value_accepted"
(* the Learner only needs to know about accepted messages to send a 'chosen' message. *)
using accepts_proposed promised_Some_accepted promised_None promised_Some proposed_quorum accepts_value
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)
  show "\<forall>p. p = p0 \<or> chosen p \<longrightarrow> (\<exists>S. quorate_learner S \<and> (\<forall>a\<in>S. accepted a p))"
    by (metis chosen_quorum assms)
qed simp_all

(* the Acceptor only needs to know what it has previously accepted and promised
to send promised messages *)
lemma (in paxosL) paxos_add_promise_None:
  assumes not_accepted: "\<And>p. \<not>accepted a0 p"
  shows   "paxosL lt le quorate_proposer quorate_learner (%a p mp. (a, p, mp) = (a0, p0, None) \<or> promised a p mp) proposed accepted chosen value_promised value_proposed value_accepted"
using assms promised_Some promised_Some_accepted promised_None chosen_quorum accepts_proposed accepts_value
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)
  show "\<forall>p. proposed p \<longrightarrow> (\<exists>S. quorate_proposer S \<and> (\<forall>a\<in>S. \<exists>mp. (a, p, mp) = (a0, p0, None) \<or> promised a p mp) \<and> (\<forall>a1\<in>S. \<forall>p1. (a1, p, Some p1) = (a0, p0, None) \<or> promised a1 p (Some p1) \<longrightarrow> value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. ((a2, p, Some p2) = (a0, p0, None) \<or> promised a2 p (Some p2)) \<and> p1 \<prec> p2)))"
  proof (intro allI impI)
    fix p assume proposed: "proposed p"
    with proposed_quorum [OF this] obtain S where S_quorate: "quorate_proposer S"
      and S_accepted: "\<And>a. a \<in> S \<Longrightarrow> EX mp. promised a p mp"
      and S_consistent: "\<And>a1 p1. \<lbrakk> a1 \<in> S; promised a1 p (Some p1) \<rbrakk> \<Longrightarrow> value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised a2 p (Some p2) \<and> p1 \<prec> p2)" by auto
      
    from S_quorate
    show "(\<exists>S. quorate_proposer S \<and> (\<forall>a\<in>S. \<exists>mp. (a, p, mp) = (a0, p0, None) \<or> promised a p mp) \<and> (\<forall>a1\<in>S. \<forall>p1. (a1, p, Some p1) = (a0, p0, None) \<or> promised a1 p (Some p1) \<longrightarrow> value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. ((a2, p, Some p2) = (a0, p0, None) \<or> promised a2 p (Some p2)) \<and> p1 \<prec> p2)))"
    proof (intro exI [where x = S] conjI ballI allI impI)
      fix a1 p1
      assume a1S: "a1 \<in> S"
      from S_accepted [OF this]
      show "\<exists>mp. (a1, p, mp) = (a0, p0, None) \<or> promised a1 p mp" by auto

      assume "(a1, p, Some p1) = (a0, p0, None) \<or> promised a1 p (Some p1)"
        hence promised: "promised a1 p (Some p1)" by simp
      from S_consistent [OF a1S promised]
      show "value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. ((a2, p, Some p2) = (a0, p0, None) \<or> promised a2 p (Some p2)) \<and> p1 \<prec> p2)"
        by auto

    qed simp
  qed
qed auto

lemma (in paxosL) paxos_add_promise_Some:
  assumes accepted: "accepted a0 p1"
  and accepted_max: "\<And>p2. accepted a0 p2 \<Longrightarrow> p2 \<preceq> p1"
  and promised_newer: "\<And>p mp. promised a0 p mp \<Longrightarrow> p \<prec> p0"
  and promised_previous_accepts: "\<And>p2. accepted a0 p2 \<Longrightarrow> p2 \<prec> p0"

  and values_eq: "value_promised a0 p0 = value_accepted a0 p1"
  shows "paxosL lt le quorate_proposer quorate_learner (%a p mp. (a, p, mp) = (a0, p0, Some p1) \<or> promised a p mp) proposed accepted chosen value_promised value_proposed value_accepted"
using assms promised_Some promised_Some_accepted promised_None chosen_quorum accepts_proposed accepts_value
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)
  show "\<forall>p. proposed p \<longrightarrow> (\<exists>S. quorate_proposer S \<and>
                            (\<forall>a2\<in>S. \<exists>mp. (a2, p, mp) = (a0, p0, Some p1) \<or> promised a2 p mp) 
                          \<and> (\<forall>a2\<in>S. \<forall>p2. (a2, p, Some p2) = (a0, p0, Some p1) \<or> promised a2 p (Some p2)
                    \<longrightarrow> value_proposed p = value_promised a2 p \<or> (\<exists>a3\<in>S. \<exists>p3. ((a3, p, Some p3) = (a0, p0, Some p1) \<or> promised a3 p (Some p3)) \<and> p2 \<prec> p3)))"
    (is "\<forall>p. proposed p \<longrightarrow> ?S_MESS p")
  proof (intro allI impI)
    fix p assume p: "proposed p"
    from proposed_quorum [OF this]
    obtain S where qS: "quorate_proposer S"
      and S_promised: "\<And>a. a \<in> S \<Longrightarrow> \<exists>mp. promised a p mp"
      and S_max: "\<And>a1 p1. \<lbrakk> a1 \<in> S; promised a1 p (Some p1) \<rbrakk> \<Longrightarrow> value_proposed p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised a2 p (Some p2) \<and> p1 \<prec> p2)" by auto
    show "?S_MESS p"
    proof (intro exI [where x = S] conjI ballI allI impI)
      from qS show "quorate_proposer S" .
      fix a2 assume a2S: "a2 \<in> S"
      with S_promised obtain mp2 where mp2: "promised a2 p mp2" by auto
      thus "\<exists>mp. (a2, p, mp) = (a0, p0, Some p1) \<or> promised a2 p mp" by auto
      fix p2 assume p2: "(a2, p, Some p2) = (a0, p0, Some p1) \<or> promised a2 p (Some p2)"
      thus "value_proposed p = value_promised a2 p \<or> (\<exists>a3\<in>S. \<exists>p3. ((a3, p, Some p3) = (a0, p0, Some p1) \<or> promised a3 p (Some p3)) \<and> p2 \<prec> p3)"
        by (metis S_max a2S mp2 prod.sel(2) promised_newer propNo_irreflexive swap_simp)
    qed
  qed

  show "\<forall>a1 p2 p3. (a1, p2, Some p3) = (a0, p0, Some p1) \<or> promised a1 p2 (Some p3) \<longrightarrow> accepted a1 p3 \<and> p3 \<prec> p2"
    by (metis accepted option.sel prod.sel(1) promised_Some_accepted promised_previous_accepts swap_simp)

  show "\<forall>a1 p2 p3 p4. (a1, p2, Some p3) = (a0, p0, Some p1) \<or> promised a1 p2 (Some p3)
      \<longrightarrow> accepted a1 p4 \<longrightarrow> p4 \<prec> p2 \<longrightarrow> p3 = p4 \<and> value_accepted a1 p3 = value_promised a1 p2 \<or> p4 \<prec> p3"
    by (metis accepted_max option.sel prod.sel(2) propNo_leE swap_simp values_eq promised_Some)
qed simp_all

(* The Acceptor only needs to know about what it's promised and accepted previously to accept a proposal *)
lemma (in paxosL) paxos_add_accepted:
  assumes proposed_p0: "proposed p0"
  assumes promised_le: "\<And>p1 mp. promised a0 p1 mp \<Longrightarrow> p1 \<preceq> p0"
  assumes proposed_val: "value_accepted a0 p0 = value_proposed p0"
  shows "paxosL lt le quorate_proposer quorate_learner promised proposed (%a p. (a, p) = (a0, p0) \<or> accepted a p) chosen value_promised value_proposed value_accepted"
using assms promised_Some promised_Some_accepted promised_None chosen_quorum accepts_proposed proposed_quorum
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)
  show "\<forall>p. chosen p \<longrightarrow> (\<exists>S. quorate_learner S \<and> (\<forall>a\<in>S. (a, p) = (a0, p0) \<or> accepted a p))"
    (is "\<forall>p. chosen p \<longrightarrow> (\<exists>S. ?P p S)")
    by (metis chosen_quorum)

  show "\<forall>a1 p1 p2. promised a1 p1 None \<longrightarrow> (a1, p2) = (a0, p0) \<or> accepted a1 p2 \<longrightarrow> p1 \<preceq> p2"
    by (metis prod.sel promised_le promised_None)

  show "\<forall>a1 p1 p2 p3. promised a1 p1 (Some p2) \<longrightarrow> (a1, p3) = (a0, p0) \<or> accepted a1 p3 \<longrightarrow> p3 \<prec> p1 \<longrightarrow> p2 = p3 \<and> value_accepted a1 p2 = value_promised a1 p1 \<or> p3 \<prec> p2"
    by (metis prod.sel promised_Some promised_le propNo_irreflexive propNo_trans_lt_le)

  show "\<forall>p a. (a, p) = (a0, p0) \<or> accepted a p \<longrightarrow> value_accepted a p = value_proposed p"
    by (metis accepts_value prod.inject proposed_val)
qed simp_all

lemma (in paxosL) paxos_change_value_promised:
  assumes accepted_eq: "\<And> a p p1. promised a p (Some p1) \<Longrightarrow> value_promised a p = value_promised' a p"
  shows "paxosL lt le quorate_proposer quorate_learner promised proposed accepted chosen value_promised' value_proposed value_accepted"
using assms promised_Some promised_Some_accepted promised_None chosen_quorum accepts_proposed proposed_quorum accepts_value
  by (unfold paxosL_def paxosL_axioms_def, simp_all)

lemma (in paxosL) paxos_change_value_proposed:
  assumes proposed_eq: "\<And> p. proposed p \<Longrightarrow> value_proposed p = value_proposed' p"
  shows "paxosL lt le quorate_proposer quorate_learner promised proposed accepted chosen value_promised value_proposed' value_accepted"
using assms promised_Some promised_Some_accepted promised_None chosen_quorum accepts_proposed proposed_quorum
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)
  show "\<forall>p. proposed p \<longrightarrow>
        (\<exists>S. quorate_proposer S \<and>
             (\<forall>a\<in>S. \<exists>mp. promised a p mp) \<and>
             (\<forall>a1\<in>S. \<forall>p1. promised a1 p (Some p1) \<longrightarrow> value_proposed' p = value_promised a1 p \<or> (\<exists>a2\<in>S. \<exists>p2. promised a2 p (Some p2) \<and> p1 \<prec> p2)))"
       (is "\<forall>p. proposed p \<longrightarrow> ?P p")
  proof (intro allI impI)
    fix p assume pp: "proposed p"
    from pp proposed_quorum [OF pp]
    show "?P p" by (unfold proposed_eq [OF pp])
  qed
    
  show "\<forall>p a. accepted a p \<longrightarrow> value_accepted a p = value_proposed' p"
    by (metis accepts_proposed accepts_value proposed_eq)
qed simp_all

lemma (in paxosL) paxos_change_value_accepted:
  assumes accepted_eq: "\<And> a p. accepted a p \<Longrightarrow> value_accepted a p = value_accepted' a p"
  shows "paxosL lt le quorate_proposer quorate_learner promised proposed accepted chosen value_promised value_proposed value_accepted'"
using assms promised_Some promised_Some_accepted promised_None chosen_quorum accepts_proposed proposed_quorum
proof (unfold paxosL_def paxosL_axioms_def, intro conjI)
  show "\<forall>p a. accepted a p \<longrightarrow> value_accepted' a p = value_proposed p"
    by (metis accepts_value assms)

  show "\<forall>a0 p0 p1 p2. promised a0 p0 (Some p1) \<longrightarrow> accepted a0 p2 \<longrightarrow> p2 \<prec> p0 \<longrightarrow> p1 = p2 \<and> value_accepted' a0 p1 = value_promised a0 p0 \<or> p2 \<prec> p1"
    by (metis assms promised_Some)
qed simp_all

