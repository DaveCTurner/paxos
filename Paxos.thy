theory Paxos
  imports Main
begin

fun propNo where "propNo ordP ltP leP
  =((ALL p1 p2. ltP p1 p2 = ((p1, p2) : ordP))
  \<and> (ALL p1 p2. leP p1 p2 = (\<not> ltP p2 p1))
  \<and> (wf ordP)
  \<and> (trans ordP)
  \<and> (ALL p1 p2. ltP p1 p2 \<or> p1 = p2 \<or> ltP p2 p1)
  )"

lemma propNo_wf: "propNo ordP ltP leP \<Longrightarrow> wf ordP" by auto

lemma
  assumes "propNo ordP ltP leP"
  shows propNo_acyclic: "acyclic ordP"
proof -
  from assms have "wf ordP" by simp
  thus ?thesis by (intro wf_acyclic)
qed

lemma propNo_cases:
  assumes propNo: "propNo ordP ltP leP"
  and lt: "ltP p1 p2 \<Longrightarrow> P"
  and eq: "p1 = p2   \<Longrightarrow> P"
  and gt: "ltP p2 p1 \<Longrightarrow> P"
  shows P
proof -
  from propNo have "ltP p1 p2 \<or> p1 = p2 \<or> ltP p2 p1" by (unfold propNo.simps, elim conjE allE)
  with lt eq gt show P by (elim disjE)
qed

lemma propNo_irreflexive:
  assumes propNo: "propNo ordP ltP leP" and refl: "ltP p1 p1"
  shows P
  using propNo_acyclic assms by auto

lemma propNo_trans_lt:
  assumes propNo: "propNo ordP ltP leP"
  and p12: "ltP p1 p2"
  and p23: "ltP p2 p3"
  shows "ltP p1 p3"
proof -
  from assms have "trans ordP" "(p1, p2) \<in> ordP" "(p2, p3) \<in> ordP" by auto
  hence "(p1, p3) \<in> ordP" by (elim transE)
  with propNo show ?thesis by simp
qed

lemma propNo_irreflexive2:
  assumes propNo: "propNo ordP ltP leP" and p12: "ltP p1 p2" and p21: "ltP p2 p1"
  shows P
proof -
  from propNo_trans_lt [OF propNo p12 p21] have "ltP p1 p1".
  with propNo propNo_irreflexive show P by auto
qed

lemma propNo_leE:
  assumes propNo: "propNo ordP ltP leP" and le: "leP p1 p2"
    and case_eq: "p1 = p2 \<Longrightarrow> P"
    and case_lt: "ltP p1 p2 \<Longrightarrow> P"
  shows P
proof (cases "p1 = p2")
  case True with case_eq show P .
next
  case False
  from le propNo have nlt: "\<not> ltP p2 p1" by simp
  from propNo have "ltP p1 p2 \<or> p1 = p2 \<or> ltP p2 p1" by (unfold propNo.simps, elim conjE allE)
  with nlt False have "ltP p1 p2" by auto
  with case_lt show P .
qed

lemma
  assumes propNo: "propNo ordP ltP leP"
  and lt: "ltP p1 p2"
  shows propNo_le_ltI: "leP p1 p2"
proof -
  have "\<not> ltP p2 p1"
  proof (intro notI)
    assume "ltP p2 p1"
    with propNo lt show False by (elim propNo_irreflexive2)
  qed
  with propNo show ?thesis by auto
qed

lemma
  assumes propNo: "propNo ordP ltP leP"
  shows le_refl: "leP p1 p1"
using assms by auto

lemma
  assumes propNo: "propNo ordP ltP leP"
  and lt: "ltP p1 p2"
  and ge: "leP p2 p1"
  shows propNo_lt_contradiction: P
using assms by auto

lemma propNo_trans_le:
  assumes propNo: "propNo ordP ltP leP"
  and p12: "leP p1 p2"
  and p23: "leP p2 p3"
  shows "leP p1 p3"
proof -
  from p12 show ?thesis
  proof (elim propNo_leE [OF propNo])
    assume "p1 = p2" with p23 show ?thesis by simp
  next
    assume p12: "ltP p1 p2"
    from p23 p12 show ?thesis
    proof (intro propNo_le_ltI [OF propNo], elim propNo_leE [OF propNo])
      assume "ltP p2 p3"
      from propNo_trans_lt [OF propNo p12 this] show "ltP p1 p3" and "ltP p1 p3" and "ltP p1 p3" by auto
    qed simp
  qed
qed

declare propNo.simps [simp del]
  
theorem
  assumes propNo: "propNo ordP ltP leP"
  assumes quorate_inter:
    "\<And> S1 S2. \<lbrakk> quorate S1; quorate S2 \<rbrakk> \<Longrightarrow> S1 \<inter> S2 \<noteq> {}"
  assumes quorate_finite: "\<And> S. quorate S \<Longrightarrow> finite S"
  assumes chosen_quorum:
    "\<And> p . chosen p \<Longrightarrow> EX S. quorate S \<and> (ALL a:S. accepted a p)"
  assumes proposed_quorum:
    "\<And> p . proposed p \<Longrightarrow> EX S. quorate S
      \<and> (ALL a:S. EX mp. promised a p mp)
      \<and> (ALL a1:S. ALL p1. promised a1 p (Some p1)
          \<longrightarrow> value p = value p1
          \<or> (EX a2:S. EX p2. promised a2 p (Some p2) \<and> ltP p1 p2))"
  assumes accepts_proposed:
    "\<And> p a. accepted a p \<Longrightarrow> proposed p"
  assumes promised_Some_accepted:
    "\<And> a p0 p1. promised a p0 (Some p1) \<Longrightarrow> accepted a p1 \<and> ltP p1 p0"
  assumes promised_Some:
    "\<And> a p0 p1 p2. \<lbrakk> promised a p0 (Some p1); accepted a p2; ltP p2 p0 \<rbrakk>
      \<Longrightarrow> ((p1 = p2 \<and> value p1 = value p0) \<or> ltP p2 p1)"
  assumes promised_None:
    "\<And> a p0 p1. \<lbrakk> promised a p0 None; accepted a p1 \<rbrakk> \<Longrightarrow> leP p0 p1"
  shows "\<And> p1 p2. \<lbrakk> chosen p1; chosen p2 \<rbrakk> \<Longrightarrow> value p1 = value p2"
proof -

  have promised_fun: "\<And>a p0 mp1 mp2. \<lbrakk> promised a p0 mp1; promised a p0 mp2 \<rbrakk> \<Longrightarrow> mp1 = mp2"
  proof -
    fix a p0
    have somenone: "\<And>p1 P. \<lbrakk> promised a p0 (Some p1); promised a p0 None \<rbrakk> \<Longrightarrow> P"
    proof -
      fix p1 P
      assume premSome: "promised a p0 (Some p1)" and premNone: "promised a p0 None"
      from propNo show P
      proof (elim propNo_lt_contradiction)
        from premSome promised_Some_accepted have acc: "accepted a p1" and ltP: "ltP p1 p0" by auto
        thus "ltP p1 p0" by simp
        from acc premNone promised_None show leP: "leP p0 p1" by auto
      qed
    qed

    fix mp1
    assume "promised a p0 mp1"
    thus "\<And>mp2. promised a p0 mp2 \<Longrightarrow> mp1 = mp2"
    proof (induct mp1)
      case (Some p1)
      thus ?case
      proof (induct mp2)
        case (Some p2)
        with promised_Some_accepted promised_Some
        have acc1: "accepted a p1" and lt1: "ltP p1 p0"
         and acc2: "accepted a p2" and lt2: "ltP p2 p0"
          by auto
        from promised_Some Some acc1 lt1 have p1: "p1 = p2 \<or> ltP p1 p2" by auto
        from promised_Some Some acc2 lt2 have p2: "p1 = p2 \<or> ltP p2 p1" by auto
        from p1 p2 show ?case
        proof (elim disjE)
          assume "ltP p1 p2" and "ltP p2 p1"
          with propNo_irreflexive2 [OF propNo] show ?thesis by auto
        qed auto
      next
        case None with somenone show ?case by auto
      qed
    next
      case None thus ?case proof (induct mp2)
        case (Some p2) with somenone show ?case by auto
      qed auto
    qed
  qed

  have p2c: "\<And>p0. proposed p0 \<Longrightarrow> EX S. quorate S \<and> 
    ((ALL a1 : S. ALL p1. ltP p1 p0 \<longrightarrow> \<not> accepted a1 p1)
    \<or> (EX a1 : S. EX p1. accepted a1 p1
        \<and> value p0 = value p1
        \<and> ltP p1 p0
        \<and> (ALL a2 : S. ALL p2. (accepted a2 p2 \<and> ltP p2 p0) \<longrightarrow> leP p2 p1)))"
  proof -
    fix p0 assume proposed_p0: "proposed p0"
    from proposed_quorum [OF this]
    obtain S where quorate_S: "quorate S"
      and S_promised: "\<And> a. a \<in> S \<Longrightarrow> \<exists>mp1. promised a p0 mp1"
      and S_value: "\<And>a1 p1. \<lbrakk> a1 \<in> S; promised a1 p0 (Some p1) \<rbrakk> \<Longrightarrow> value p0 = value p1 \<or> (\<exists>a2\<in>S. \<exists>p2. promised a2 p0 (Some p2) \<and> ltP p1 p2)"
      by auto
    show "?thesis p0"
    proof (cases "ALL a1:S. promised a1 p0 None")
      case True
      hence no_accept: "\<And> a1. \<lbrakk> a1 \<in> S \<rbrakk> \<Longrightarrow> promised a1 p0 None" by simp
      from propNo show ?thesis
      proof (intro exI conjI disjI1 ballI impI allI notI)
        from quorate_S show "quorate S" .
        fix a1 p1 assume a1S: "a1 \<in> S" and lt10: "ltP p1 p0" and acc1: "accepted a1 p1"
        from propNo lt10 show False
        proof (elim propNo_lt_contradiction)
          from promised_None no_accept a1S acc1 show "leP p0 p1" by auto
        qed
      qed
    next
      case False
      then obtain a2 where a2S: "a2 \<in> S" and not_None: "\<not> promised a2 p0 None" by auto
      from S_promised a2S obtain mp2 where "promised a2 p0 mp2" by auto
      with not_None obtain p2 where p2: "promised a2 p0 (Some p2)"
        by (cases mp2, auto)

      from quorate_finite quorate_S have "finite S".
      hence "(ALL a1:S. ALL mp. promised a1 p0 mp \<longrightarrow> mp = None) \<or> (EX a1:S. EX p1. promised a1 p0 (Some p1) \<and> (ALL a3:S. ALL p3. promised a3 p0 (Some p3) \<longrightarrow> leP p3 p1))"
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
              and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S'; promised a3 p0 (Some p3) \<rbrakk> \<Longrightarrow> leP p3 p1"
              by auto
            
            show ?thesis
            proof (intro disjI2 bexI exI conjI ballI allI impI)
              from p show "promised a1 p0 (Some p1)" .
              from a1S show "a1 \<in> insert a S'" by simp
              fix a3 p3
              assume a3S: "a3 \<in> insert a S'"
                and p3: "promised a3 p0 (Some p3)"
              show "leP p3 p1"
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
                and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S'; promised a3 p0 (Some p3) \<rbrakk> \<Longrightarrow> leP p3 p1"
                by auto
              show ?thesis
              proof (intro disjI2 bexI exI conjI impI ballI allI)
                from p show "promised a1 p0 (Some p1)" .
                from a1S show "a1 \<in> insert a S'" by simp
                fix a3 p3 assume "a3 \<in> insert a S'" and p: "promised a3 p0 (Some p3)"
                hence "a3 = a \<or> a3 \<in> S'" by simp
                thus "leP p3 p1"
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
                hence "p = p3" by simp
                with le_refl [OF propNo] show "leP p3 p" by simp
              qed
            next
              assume "?P2 S'"
              then obtain a1 p1 where a1S: "a1 \<in> S'" and p: "promised a1 p0 (Some p1)"
                and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S'; promised a3 p0 (Some p3) \<rbrakk> \<Longrightarrow> leP p3 p1" by auto
              from propNo
              show ?thesis
              proof (elim propNo_cases)
                assume p1p: "p1 = p"
                show ?thesis
                proof (intro bexI exI conjI ballI allI impI)
                  from p show "promised a1 p0 (Some p1)" .
                  from a1S show "a1 \<in> insert a S'" by simp
                  fix a3 p3
                  assume "a3 \<in> insert a S'"
                    and p3: "promised a3 p0 (Some p3)"
                  hence "a3 = a \<or> a3 \<in> S'" by simp
                  thus "leP p3 p1"
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
                    with le_refl [OF propNo] p1p show "leP p3 p1" by simp
                  qed
                qed
              next
                assume pp1: "ltP p p1"
                show ?thesis
                proof (intro bexI exI conjI ballI allI impI)
                from p show "promised a1 p0 (Some p1)" .
                from a1S show "a1 \<in> insert a S'" by simp
                  fix a3 p3
                  assume "a3 \<in> insert a S'"
                    and p3: "promised a3 p0 (Some p3)"
                  hence "a3 = a \<or> a3 \<in> S'" by simp
                  thus "leP p3 p1"
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
                    with pp1 have "ltP p3 p1" by simp
                    thus "leP p3 p1" by (intro propNo_le_ltI [OF propNo])
                  qed
                qed
              next
                assume "ltP p1 p"
                show ?thesis sorry
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
        and p1_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S; promised a3 p0 (Some p3) \<rbrakk> \<Longrightarrow> leP p3 p1" by auto

      from p1 promised_Some_accepted have lt10: "ltP p1 p0" by auto

      show ?thesis
      proof (intro exI conjI disjI2 bexI ballI allI impI)
        from quorate_S show "quorate S" .
        from p1 promised_Some_accepted show "accepted a1 p1" by simp
        from a1S show "a1 \<in> S" .
        from S_value [OF a1S p1]
        show "value p0 = value p1"
        proof (elim disjE bexE exE conjE)
          fix a3 p3 assume a3S: "a3 \<in> S" and p3: "promised a3 p0 (Some p3)" and lt13: "ltP p1 p3"
          with p1_max propNo show ?thesis by (elim propNo_lt_contradiction, auto)
        qed
        from lt10 show "ltP p1 p0" .

        fix a3 p3 assume a3S: "a3 \<in> S" and "accepted a3 p3 \<and> ltP p3 p0"
        hence acc3: "accepted a3 p3" and lt30: "ltP p3 p0" by auto

        from a3S S_promised obtain mp3 where mp3: "promised a3 p0 mp3" by auto
        show "leP p3 p1"
        proof (cases mp3)
          case None
          with mp3 have "promised a3 p0 None" by simp
          from promised_None [OF this acc3] lt30 propNo show ?thesis by (elim propNo_lt_contradiction, auto)
        next
          case (Some p3')
          show ?thesis
          proof (rule propNo_trans_le [OF propNo])
            from Some mp3 have p3': "promised a3 p0 (Some p3')" by simp
            from p3' a3S show "leP p3' p1" by (intro p1_max)
            from promised_Some [OF p3' acc3 lt30]
            have "p3' = p3 \<or> ltP p3 p3'" by auto
            thus "leP p3 p3'"
            proof (elim disjE)
              assume "p3' = p3" with le_refl [OF propNo] show ?thesis by auto
            next
              assume "ltP p3 p3'"
              thus ?thesis by (intro propNo_le_ltI [OF propNo])
            qed
          qed
        qed
      qed
    qed
  qed

  have p2b: "\<And>p0 p1. \<lbrakk> chosen p0; proposed p1; leP p0 p1 \<rbrakk> \<Longrightarrow> value p0 = value p1"
  proof -
    fix p0 p1_base

    assume chosen: "chosen p0"
    from chosen_quorum [OF chosen] obtain SC
      where SC_quorate: "quorate SC"
      and SC_accepts: "\<And>a. \<lbrakk> a \<in> SC \<rbrakk> \<Longrightarrow> accepted a p0" by auto

    assume "proposed p1_base" "leP p0 p1_base" thus "?thesis p0 p1_base"
    proof (induct p1_base rule: wf_induct [OF propNo_wf [OF propNo]])
      fix p1
      assume proposed: "proposed p1" and le01: "leP p0 p1"
      assume "\<forall>p2. (p2, p1) \<in> ordP \<longrightarrow> proposed p2 \<longrightarrow> leP p0 p2 \<longrightarrow> value p0 = value p2" 
        with propNo have
        hyp: "\<And>p2. \<lbrakk> ltP p2 p1; proposed p2; leP p0 p2 \<rbrakk> \<Longrightarrow> value p0 = value p2" by (auto simp add: propNo.simps)

      from le01
      show "value p0 = value p1"
      proof (elim propNo_leE [OF propNo])
        assume lt01: "ltP p0 p1"
        show ?thesis
        proof -
  
          from p2c [OF proposed] obtain S where S_quorate: "quorate S"
            and S_mess: "((\<forall>a1\<in>S. \<forall>p1a. ltP p1a p1 \<longrightarrow> \<not> accepted a1 p1a)
            \<or> (\<exists>a1\<in>S. \<exists>p1a. accepted a1 p1a \<and> value p1 = value p1a \<and> ltP p1a p1
                \<and> (\<forall>a2\<in>S. \<forall>p2. accepted a2 p2 \<and> ltP p2 p1 \<longrightarrow> leP p2 p1a)))"
            (is "?P1 \<or> ?P2") by auto
    
          from S_quorate SC_quorate quorate_inter obtain a where aS: "a \<in> S" and aSC: "a \<in> SC" by auto
  
          from S_mess
          show "value p0 = value p1"
          proof (elim disjE)
            assume "?P1"
            hence 1: "\<And>a2 p2 P. \<lbrakk> a2 \<in> S; ltP p2 p1; accepted a2 p2 \<rbrakk> \<Longrightarrow> P" by auto
            show ?thesis by (rule 1 [OF aS lt01 SC_accepts [OF aSC]])
          next
            assume "?P2"
            then obtain a2 p2 where a2S: "a2 \<in> S"
              and a2_accepted: "accepted a2 p2"
              and v_eq: "value p1 = value p2"
              and a2_max: "\<And>a3 p3. \<lbrakk> a3 \<in> S; accepted a3 p3; ltP p3 p1 \<rbrakk> \<Longrightarrow> leP p3 p2"
              and lt21: "ltP p2 p1"
              by auto
            
            from aS aSC
            have "value p0 = value p2"
             by (intro hyp a2_max lt01 SC_accepts accepts_proposed [OF a2_accepted] lt21)
            with v_eq show "value p0 = value p1" by simp
          qed
        qed
      qed simp
    qed
  qed

  have p2a: "\<And>p0 p1 a1. \<lbrakk> chosen p0; accepted a1 p1; leP p0 p1 \<rbrakk> \<Longrightarrow> value p0 = value p1"
    by (intro p2b accepts_proposed)

  have p2: "\<And>p0 p1. \<lbrakk> chosen p0; chosen p1; leP p0 p1 \<rbrakk> \<Longrightarrow> value p0 = value p1"
  proof -
    fix p1
    assume "chosen p1"
    from chosen_quorum [OF this] obtain SC
      where SC_quorate: "quorate SC"
      and SC_accepts: "\<And>a. \<lbrakk> a \<in> SC \<rbrakk> \<Longrightarrow> accepted a p1" by auto

    from SC_quorate quorate_inter
    obtain a where aSC: "a \<in> SC" by auto
    from SC_accepts [OF this] have acc: "accepted a p1" .

    from acc
    show "\<And> p0. \<lbrakk> chosen p0; leP p0 p1 \<rbrakk> \<Longrightarrow> ?thesis p0 p1" by (intro p2a)
  qed

  fix p1 p2
  assume cp1: "chosen p1" and cp2: "chosen p2"
  show "value p1 = value p2"
  proof (cases rule: propNo_cases [OF propNo])
    assume "p1 = p2" thus "value p1 = value p2" by simp
  next
    assume "ltP p1 p2" hence "leP p1 p2" by (intro propNo_le_ltI [OF propNo])
    with cp1 cp2 show ?thesis by (intro p2)
  next
    assume "ltP p2 p1" hence "leP p2 p1" by (intro propNo_le_ltI [OF propNo])
    with cp1 cp2 have "value p2 = value p1" by (intro p2)
    thus ?thesis by simp
  qed
qed


