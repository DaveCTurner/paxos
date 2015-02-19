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
  using assms local.le_lt_eq by (auto)

lemma (in propNoL) propNo_irreflexive [simp]:
  shows "\<not> p \<prec> p"
proof
  assume pp: "p \<prec> p"
  hence "(p,p) \<in> {(p1,p2). p1 \<prec> p2}" by simp
  also have "... \<subseteq> trancl ..." by auto
  finally have "(p,p) \<in> ..." .
  with propNo_acyclic show False by (auto simp add: acyclic_def)
qed 

lemma (in propNoL) propNo_trans_lt_lt [trans]:
  "p1 \<prec> p2 \<Longrightarrow> p2 \<prec> p3 \<Longrightarrow> p1 \<prec> p3"
  using trans by (elim transE, auto)

lemma (in propNoL) propNo_lt_not_ge_E [elim]:
  assumes lt: "p1 \<prec> p2"
  and not_gt: "\<lbrakk> p1 \<noteq> p2; \<not>(p2 \<prec> p1) \<rbrakk>  \<Longrightarrow> P"
  shows P
using lt
proof (intro not_gt notI)
  assume "p2 \<prec> p1" also note lt
  finally show False by auto
qed auto

lemma (in propNoL) propNo_trans_lt_le [trans]:
  "p1 \<prec> p2 \<Longrightarrow> p2 \<preceq> p3 \<Longrightarrow> p1 \<prec> p3"
  by (elim propNo_leE, rule propNo_trans_lt_lt, simp_all)

lemma (in propNoL) propNo_trans_le_lt [trans]:
  "p1 \<preceq> p2 \<Longrightarrow> p2 \<prec> p3 \<Longrightarrow> p1 \<prec> p3"
  by (elim propNo_leE, rule propNo_trans_lt_lt, simp_all)

lemma (in propNoL) propNo_trans_le_le [trans]:
  assumes p12: "p1 \<preceq> p2" and p23: "p2 \<preceq> p3"
  shows "p1 \<preceq> p3"
proof (cases "p1 = p3")
  case True thus ?thesis by simp
next
  case False
  with p12 p23
  show "p1 \<preceq> p3"
  proof (elim propNo_leE)
    assume "p1 \<prec> p2"
    also assume "p2 \<prec> p3"
    finally show ?thesis by simp
  qed auto
qed

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
  fixes "value" :: "'pid \<Rightarrow> 'value"

  assumes chosen_quorum:
    "\<And> p . chosen p \<Longrightarrow> EX S. quorate_learner S \<and> (ALL a:S. accepted a p)"
  assumes proposed_quorum:
    "\<And> p . proposed p \<Longrightarrow> EX S. quorate_proposer S
      \<and> (ALL a:S. EX mp. promised a p mp)
      \<and> (ALL a1:S. ALL p1. promised a1 p (Some p1)
          \<longrightarrow> value p = value p1
          \<or> (EX a2:S. EX p2. promised a2 p (Some p2) \<and> p1 \<prec> p2))"
  assumes accepts_proposed:
    "\<And> p a. accepted a p \<Longrightarrow> proposed p"
  assumes promised_Some_accepted:
    "\<And> a p0 p1. promised a p0 (Some p1) \<Longrightarrow> accepted a p1 \<and> p1 \<prec> p0"
  assumes promised_Some:
    "\<And> a p0 p1 p2. \<lbrakk> promised a p0 (Some p1); accepted a p2; p2 \<prec> p0 \<rbrakk>
      \<Longrightarrow> ((p1 = p2 \<and> value p1 = value p0) \<or> p2 \<prec> p1)"
  assumes promised_None:
    "\<And> a p0 p1. \<lbrakk> promised a p0 None; accepted a p1 \<rbrakk> \<Longrightarrow> p0 \<preceq> p1"

lemma (in paxosL) promised_some_none:
  assumes premSome: "promised a p0 (Some p1)" and premNone: "promised a p0 None"
  shows P
proof -
  from premSome promised_Some_accepted
  have acc: "accepted a p1" and p10: "p1 \<prec> p0" by auto
  from premNone acc promised_None
  have p01: "p0 \<preceq> p1" by auto
  also note p10
  finally show P by auto
qed

lemma (in paxosL) promised_fun:
  assumes mp1: "promised a p0 mp1" and mp2: "promised a p0 mp2"
  shows "mp1 = mp2"
proof (cases mp1)
  case None
  note None1 = this
  thus ?thesis
  proof (cases mp2)
    case (Some p2) show ?thesis
    proof (rule promised_some_none)
      from mp2 Some show "promised a p0 (Some p2)" by simp
      from mp1 None1 show "promised a p0 None" by simp
    qed 
  qed simp
next
  case (Some p1) note Some1 = this
  show ?thesis
  proof (cases mp2)
    case None show ?thesis
    proof (rule promised_some_none)
      from mp1 Some show "promised a p0 (Some p1)" by simp
      from mp2 None show "promised a p0 None" by simp
    qed
  next
    case (Some p2) note Some2 = this
    from mp1 mp2 Some1 Some2 promised_Some_accepted promised_Some
    have acc1: "accepted a p1" and p10: "p1 \<prec> p0"
     and acc2: "accepted a p2" and p20: "p2 \<prec> p0"
      by auto
    from mp1 promised_Some Some1 acc2 p20 have p12: "p2 \<preceq> p1" by auto
    from mp2 promised_Some Some2 acc1 p10 have p21: "p1 \<preceq> p2" by auto
    from p12 p21
    have "p1 = p2"
    proof (elim propNo_leE)
      assume "p1 \<prec> p2"
      also assume "p2 \<prec> p1"
      finally show ?thesis by auto
    qed simp_all
    with Some1 Some2 show ?thesis by simp
  qed
qed

lemma (in paxosL) p2c:
  assumes proposed_p0: "proposed p0"
  obtains S where "quorate_proposer S"
    and "(ALL a1 : S. ALL p1. p1 \<prec> p0 \<longrightarrow> \<not> accepted a1 p1)
    \<or> (EX a1 : S. EX p1. accepted a1 p1
        \<and> value p0 = value p1
        \<and> p1 \<prec> p0
        \<and> (ALL a2 : S. ALL p2. (accepted a2 p2 \<and> p2 \<prec> p0) \<longrightarrow> p2 \<preceq> p1))"
proof -
  from proposed_quorum [OF proposed_p0]
  obtain S where quorate_S: "quorate_proposer S"
    and S_promised: "\<And> a1. a1 \<in> S \<Longrightarrow> \<exists>mp1. promised a1 p0 mp1"
    and S_value: "\<And>a1 p1. \<lbrakk> a1 \<in> S; promised a1 p0 (Some p1) \<rbrakk> \<Longrightarrow> value p0 = value p1 \<or> (\<exists>a2\<in>S. \<exists>p2. promised a2 p0 (Some p2) \<and> p1 \<prec> p2)"
    by auto
  show thesis
  proof (intro that)
    from quorate_S show "quorate_proposer S" .
    show "(ALL a1 : S. ALL p1. p1 \<prec> p0 \<longrightarrow> \<not> accepted a1 p1)
        \<or> (EX a1 : S. EX p1. accepted a1 p1
            \<and> value p0 = value p1
            \<and> p1 \<prec> p0
            \<and> (ALL a2 : S. ALL p2. (accepted a2 p2 \<and> p2 \<prec> p0) \<longrightarrow> p2 \<preceq> p1))"
    (is "?ALLFRESH \<or> ?EXISTSMAX")
    proof (cases "ALL a1:S. promised a1 p0 None")
      case True
      show ?thesis
      proof (intro disjI1 ballI allI impI notI)
        fix a1 p1 assume a1S: "a1 \<in> S" and p10: "p1 \<prec> p0" and acc1: "accepted a1 p1"
        from a1S promised_None True acc1 have "p0 \<preceq> p1" by auto
        also note p10
        finally show False by auto
      qed
    next
      case False
      then obtain a2 where a2S: "a2 \<in> S" and not_None: "\<not> promised a2 p0 None" by auto
      from S_promised a2S obtain mp2 where "promised a2 p0 mp2" by auto
      with not_None obtain p2 where p2: "promised a2 p0 (Some p2)"
        by (cases mp2, auto)
  
      from quorate_finite quorate_S have "finite S".
      hence "(ALL a1:S. ALL mp. promised a1 p0 mp \<longrightarrow> mp = None) \<or> (EX a1:S. EX p1. promised a1 p0 (Some p1) \<and> (ALL a3:S. ALL p3. promised a3 p0 (Some p3) \<longrightarrow> p3 \<preceq> p1))"
        (is "?P1 S \<or> ?P2 S")
      proof (induct S rule: finite_induct)
        case empty thus ?case by simp
      next
        case (insert a S')
  
        show "?P1 (insert a S') \<or> ?P2 (insert a S')"
        proof (cases "EX mp. promised a p0 mp")
          case False
          from insert.hyps
          show ?thesis
          proof (elim disjE)
            assume hyp1: "?P1 S'"
            show ?thesis
            proof (intro disjI1 ballI allI impI)
              fix a1 mp assume "a1 \<in> insert a S'" and p: "promised a1 p0 mp"
              with False have "a1 \<in> S'" by auto
              from hyp1 this p show "mp = None" by auto
            qed
          next
            assume hyp2: "?P2 S'"
            then obtain a1 p1 where a1S: "a1 \<in> S'" and p: "promised a1 p0 (Some p1)"
              and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S'; promised a3 p0 (Some p3) \<rbrakk> \<Longrightarrow> p3 \<preceq> p1"
              by auto
            
            show ?thesis
            proof (intro disjI2 bexI exI conjI ballI allI impI)
              from p show "promised a1 p0 (Some p1)" .
              from a1S show "a1 \<in> insert a S'" by simp
              fix a3 p3
              assume a3S: "a3 \<in> insert a S'"
                and p3: "promised a3 p0 (Some p3)"
              show "p3 \<preceq> p1"
              proof (intro p1_max)
                from p3 show "promised a3 p0 (Some p3)" .
                from a3S False p3 show "a3 \<in> S'" by auto
              qed
            qed
          qed
        next
          case True
          then obtain mp where mp: "promised a p0 mp" by auto
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
                assume "a1 \<in> insert a S'" and p: "promised a1 p0 mp'"
                hence "a1 = a \<or> a1 \<in> S'" by simp
                thus "mp' = None"
                proof (elim disjE)
                  assume eq: "a1 = a"
                  show "mp' = None"
                  proof (intro promised_fun)
                    from mp None show "promised a p0 None" by simp
                    from eq p show "promised a p0 mp'" by simp
                  qed
                next
                  assume mem: "a1 \<in> S'"
                  from hyp1 mem p
                  show "mp' = None" by auto
                qed
              qed
            next
              assume hyp2: "?P2 S'"
              then obtain a1 p1 where a1S: "a1 \<in> S'" and p: "promised a1 p0 (Some p1)"
                and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S'; promised a3 p0 (Some p3) \<rbrakk> \<Longrightarrow> p3 \<preceq> p1"
                by auto
              show ?thesis
              proof (intro disjI2 bexI exI conjI impI ballI allI)
                from p show "promised a1 p0 (Some p1)" .
                from a1S show "a1 \<in> insert a S'" by simp
                fix a3 p3 assume "a3 \<in> insert a S'" and p: "promised a3 p0 (Some p3)"
                hence "a3 = a \<or> a3 \<in> S'" by simp
                thus "p3 \<preceq> p1"
                proof (elim disjE)
                  assume "a3 = a"
                  with p have p: "promised a p0 (Some p3)" by simp
                  have "Some p3 = mp" by (intro promised_fun [OF p mp])
                  with None show ?thesis by simp
                next
                  assume a3: "a3 \<in> S'"
                  with p show ?thesis by (intro p1_max, auto)
                qed
              qed
            qed
          next
            case (Some p)
            
            from insert.hyps
            have "?P2 (insert a S')"
            proof (elim disjE)
              assume "?P1 S'"
              hence none_proposed: "\<And> a1 mp. \<lbrakk> a1 \<in> S'; promised a1 p0 mp \<rbrakk> \<Longrightarrow> mp = None" by simp
              show ?thesis
              proof (intro bexI exI conjI impI ballI allI)
                show "a \<in> insert a S'" by simp
                from mp Some show "promised a p0 (Some p)" by simp
                fix a3 p3
                assume "a3 \<in> insert a S'" and p: "promised a3 p0 (Some p3)"
                with none_proposed have a3: "a3 = a" by auto
                have "Some p = Some p3"
                proof (intro promised_fun)
                  from p show "promised a3 p0 (Some p3)" .
                  from a3 Some mp show "promised a3 p0 (Some p)" by simp
                qed
                thus "p3 \<preceq> p" by simp
              qed
            next
              assume "?P2 S'"
              then obtain a1 p1 where a1S: "a1 \<in> S'" and p: "promised a1 p0 (Some p1)"
                and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S'; promised a3 p0 (Some p3) \<rbrakk> \<Longrightarrow> p3 \<preceq> p1" by auto
              show ?thesis
              proof (rule propNo_cases)
                assume p1p: "p1 = p"
                show ?thesis
                proof (intro bexI exI conjI ballI allI impI)
                  from p show "promised a1 p0 (Some p1)" .
                  from a1S show "a1 \<in> insert a S'" by simp
                  fix a3 p3
                  assume "a3 \<in> insert a S'"
                    and p3: "promised a3 p0 (Some p3)"
                  hence "a3 = a \<or> a3 \<in> S'" by simp
                  thus "p3 \<preceq> p1"
                  proof (elim disjE)
                    assume a3: "a3 \<in> S'"
                    show ?thesis by (intro p1_max [OF a3] p3)
                  next
                    assume a3: "a3 = a"
                    have "Some p = Some p3"
                    proof (intro promised_fun)
                      from p3 show "promised a3 p0 (Some p3)" .
                      from a3 Some mp show "promised a3 p0 (Some p)" by simp
                    qed
                    with p1p show ?thesis by simp
                  qed
                qed
              next
                assume pp1: "p \<prec> p1"
                show ?thesis
                proof (intro bexI exI conjI ballI allI impI)
                from p show "promised a1 p0 (Some p1)" .
                from a1S show "a1 \<in> insert a S'" by simp
                  fix a3 p3
                  assume "a3 \<in> insert a S'"
                    and p3: "promised a3 p0 (Some p3)"
                  hence "a3 = a \<or> a3 \<in> S'" by simp
                  thus "p3 \<preceq> p1"
                  proof (elim disjE)
                    assume a3: "a3 \<in> S'"
                    show ?thesis by (intro p1_max [OF a3] p3)
                  next
                    assume a3: "a3 = a"
                    have "Some p = Some p3"
                    proof (intro promised_fun)
                      from p3 show "promised a3 p0 (Some p3)" .
                      from a3 Some mp show "promised a3 p0 (Some p)" by simp
                    qed
                    hence "p = p3" by simp
                    with pp1 show ?thesis by simp
                  qed
                qed
              next
                assume p1p: "p1 \<prec> p"
                show ?thesis
                proof (intro bexI exI conjI ballI allI impI)
                  from mp Some show "promised a p0 (Some p)" by simp
                  show "a \<in> insert a S'" by simp
                  fix a3 p3
                  assume "a3 \<in> insert a S'"
                    and p3: "promised a3 p0 (Some p3)"
                  hence "a3 = a \<or> a3 \<in> S'" by simp
                  thus "p3 \<preceq> p"
                  proof (elim disjE)
                    assume a3: "a3 = a"
                    have "Some p3 = Some p"
                    proof (intro promised_fun [OF p3])
                      from a3 mp Some show "promised a3 p0 (Some p)" by simp
                    qed
                    thus ?thesis by simp
                  next
                    assume a3: "a3 \<in> S'"
                    with p3 have "p3 \<preceq> p1" by (intro p1_max)
                    also note p1p
                    finally show ?thesis by simp
                  qed
                qed
              qed
            qed
  
            thus ?thesis by simp
          qed
        qed
      qed
  
      from this have "?P2 S"
      proof (elim disjE)
        assume "?P1 S" with a2S p2 show ?thesis by auto
      qed
  
      from this obtain a1 p1
        where a1S: "a1 \<in> S"
        and p1: "promised a1 p0 (Some p1)"
        and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S; promised a3 p0 (Some p3) \<rbrakk> \<Longrightarrow> p3 \<preceq> p1" by auto
  
      from p1 promised_Some_accepted have lt10: "p1 \<prec> p0" by auto
  
      show ?thesis
      proof (intro exI conjI disjI2 bexI ballI allI impI)
        from p1 promised_Some_accepted show "accepted a1 p1" by simp
        from a1S show "a1 \<in> S" .
        from S_value [OF a1S p1]
        show "value p0 = value p1"
        proof (elim disjE bexE exE conjE)
          fix a3 p3 assume "a3 \<in> S" and "promised a3 p0 (Some p3)"
          with p1_max have "p3 \<preceq> p1" by auto
          also assume "p1 \<prec> p3"
          finally show ?thesis by auto
        qed
        from lt10 show "p1 \<prec> p0" .
  
        fix a3 p3 assume a3S: "a3 \<in> S" and "accepted a3 p3 \<and> p3 \<prec> p0"
        hence acc3: "accepted a3 p3" and lt30: "p3 \<prec> p0" by auto
  
        from a3S S_promised obtain mp3 where mp3: "promised a3 p0 mp3" by auto
        show "p3 \<preceq> p1"
        proof (cases mp3)
          case None
          with mp3 have "promised a3 p0 None" by simp
          with promised_None acc3 lt30 show ?thesis by auto
        next
          case (Some p3')
          from mp3 Some have "promised a3 p0 (Some p3')" by simp
          from promised_Some [OF this] acc3 lt30 have "p3 \<preceq> p3'" by auto
          also from p1_max a3S mp3 Some have "p3' \<preceq> p1" by auto
          finally show ?thesis .
        qed
      qed
    qed
  qed
qed

lemma (in paxosL) p2b: 
  assumes chosen: "chosen p0"
  shows "\<And>p1. \<lbrakk> proposed p1; p0 \<preceq> p1 \<rbrakk> \<Longrightarrow> value p0 = value p1"
proof -
  from chosen_quorum [OF chosen] obtain SL
    where SC_quorate: "quorate_learner SL"
    and SC_accepts: "\<And>a. \<lbrakk> a \<in> SL \<rbrakk> \<Longrightarrow> accepted a p0" by auto

  fix p1_base
  assume "proposed p1_base" "p0 \<preceq> p1_base" thus "?thesis p1_base"
  proof (induct p1_base rule: wf_induct [OF wf])
    fix p1
    assume proposed: "proposed p1" and p01: "p0 \<preceq> p1"
    assume "\<forall>p2. (p2, p1) \<in> {(p,q). p \<prec> q} \<longrightarrow> proposed p2 \<longrightarrow> p0 \<preceq> p2 \<longrightarrow> value p0 = value p2"
      hence
      hyp: "\<And>p2. \<lbrakk> p2 \<prec> p1; proposed p2; p0 \<preceq> p2 \<rbrakk> \<Longrightarrow> value p0 = value p2" by auto

    from p01
    show "value p0 = value p1"
    proof (elim propNo_leE)
      assume lt01: "p0 \<prec> p1"
      show ?thesis
      proof -

        from p2c [OF proposed] obtain SP where SP_quorate: "quorate_proposer SP"
          and S_mess: "((\<forall>a1\<in>SP. \<forall>p1a. p1a \<prec> p1 \<longrightarrow> \<not> accepted a1 p1a)
          \<or> (\<exists>a1\<in>SP. \<exists>p1a. accepted a1 p1a \<and> value p1 = value p1a \<and> p1a \<prec> p1
              \<and> (\<forall>a2\<in>SP. \<forall>p2. accepted a2 p2 \<and> p2 \<prec> p1 \<longrightarrow> p2 \<preceq> p1a)))"
          (is "?P1 \<or> ?P2") by auto
  
        from SP_quorate SC_quorate quorate_inter
        obtain a where aSP: "a \<in> SP" and aSC: "a \<in> SL" by auto

        from S_mess
        show "value p0 = value p1"
        proof (elim disjE)
          assume "?P1"
          hence 1: "\<And>a2 p2 P. \<lbrakk> a2 \<in> SP; p2 \<prec> p1; accepted a2 p2 \<rbrakk> \<Longrightarrow> P" by auto
          show ?thesis by (rule 1 [OF aSP lt01 SC_accepts [OF aSC]])
        next
          assume "?P2"
          then obtain a2 p2 where a2S: "a2 \<in> SP"
            and a2_accepted: "accepted a2 p2"
            and v_eq: "value p1 = value p2"
            and a2_max: "\<And>a3 p3. \<lbrakk> a3 \<in> SP; accepted a3 p3; p3 \<prec> p1 \<rbrakk> \<Longrightarrow> p3 \<preceq> p2"
            and lt21: "p2 \<prec> p1"
            by auto
          
          from aSP aSC
          have "value p0 = value p2"
           by (intro hyp a2_max lt01 SC_accepts accepts_proposed [OF a2_accepted] lt21)
          with v_eq show "value p0 = value p1" by simp
        qed
      qed
    qed simp
  qed
qed

lemma (in paxosL)
  assumes "chosen p0" and "accepted a1 p1" and "p0 \<preceq> p1"
  shows p2a: "value p0 = value p1"
using assms by (intro p2b accepts_proposed)

lemma (in paxosL)
  assumes chosen0: "chosen p0"
  assumes chosen1: "chosen p1"
  assumes p01: "p0 \<preceq> p1"
  shows p2: "value p0 = value p1"
proof -
  from chosen_quorum [OF chosen1] obtain SC
    where SC_quorate: "quorate_learner SC"
    and SC_accepts: "\<And>a. \<lbrakk> a \<in> SC \<rbrakk> \<Longrightarrow> accepted a p1" by auto

  from quorum_exists obtain SP where "quorate_proposer SP" by auto
  with SC_quorate quorate_inter
  obtain a where aSC: "a \<in> SC" by auto
  from SC_accepts [OF this] have acc: "accepted a p1" .

  from acc chosen0 p01
  show "value p0 = value p1"
    by (intro p2a)
qed

theorem (in paxosL)
  assumes chosen0: "chosen p0"
  assumes chosen1: "chosen p1"
  shows paxos_consistent: "value p0 = value p1"
proof (cases rule: propNo_cases)
  assume "p0 \<prec> p1" hence "p0 \<preceq> p1" by simp
  with chosen0 chosen1 show ?thesis by (intro p2)
next
  assume "p1 \<prec> p0" hence "p1 \<preceq> p0" by simp
  with chosen0 chosen1 show ?thesis by (intro sym [OF p2])
qed simp

