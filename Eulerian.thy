theory Eulerian imports
  "~~/src/HOL/Library/Multiset"
begin

type_synonym 'node graph = "('node \<times> 'node) multiset"

definition inDegree :: "'node graph \<Rightarrow> 'node \<Rightarrow> nat"
  where "inDegree G n = size {# e \<in># G . snd e = n #}"

definition outDegree :: "'node graph \<Rightarrow> 'node \<Rightarrow> nat"
  where "outDegree G n = size {# e \<in># G . fst e = n #}"

definition nodes :: "'node graph \<Rightarrow> 'node set"
  where "nodes G = fst ` (set_of G) \<union> snd ` (set_of G)"

definition path :: "'node graph \<Rightarrow> ('node \<times> 'node) list \<Rightarrow> bool"
  where "path G p \<equiv> (set p \<subseteq> set_of G) \<and> (\<forall>i. (i + 1 < length p) \<longrightarrow> (snd (p ! i) = fst (p ! (i + 1))))"

definition eulerPath :: "'node graph \<Rightarrow> ('node \<times> 'node) list \<Rightarrow> bool"
  where "eulerPath G es = ((path G es) \<and> fst (hd es) = snd (last es) \<and> G = multiset_of es)"

definition strongly_connected :: "'node graph \<Rightarrow> bool"
  where "strongly_connected G = (\<forall>n. n \<in> (nodes G) \<longrightarrow> (\<forall>m. m \<in> (nodes G) \<longrightarrow>
         (\<exists>p. path G p \<and> fst (hd p) = n \<and> snd (last p) = m)))"

definition eulerian :: "'node graph \<Rightarrow> bool"
  where "eulerian G = (\<exists>es. eulerPath G es)"

lemma multiset_not_emptyE:
  assumes "M \<noteq> {#}"
  obtains x where "x \<in># M"
using assms by (cases M)(force split:split_if_asm)+

lemma obtainNode:
  assumes "n \<in> (nodes G)"
  obtains e where "e \<in># G \<and> (fst e = n \<or> snd e = n)"
using assms
proof-
  assume a1:"(\<And>e. e \<in># G \<and> (fst e = n \<or> snd e = n) \<Longrightarrow>
         thesis)"
  assume "n \<in> nodes G"
  hence "n \<in> fst ` (set_of G) \<or>  n \<in> snd ` (set_of G)"
    by (simp add:nodes_def)
    thus thesis
  proof(rule disjE)
    assume "n \<in> fst ` set_of G" 
    hence "\<exists>e. e \<in># G \<and> n = fst e" by auto
    then obtain e where "e \<in># G \<and> n = fst e" by (rule exE)
    hence "e \<in># G \<and> (fst e = n \<or> snd e = n)" by simp
    with a1 show thesis.
  next
    assume "n \<in> snd ` set_of G"
    hence "\<exists>e. e \<in># G \<and> n = snd e" by auto
    then obtain e where "e \<in># G \<and> n = snd e" by (rule exE)
    hence "e \<in># G \<and> (fst e = n \<or> snd e = n)" by simp
    with a1 show thesis.
  qed
qed

lemma subPathDrop:
  assumes "path G p"
  shows "path G (drop i p)"
using assms proof-
  have "set (drop i p) \<subseteq>  set p" by (simp add:List.set_drop_subset)
  also
  from `path G p` have "set p \<subseteq> set_of G" by (simp add:path_def)
  finally
  have t1:"set (drop i p) \<le> set_of G".
  have t2:"\<forall>j. (j + 1 < length (drop i p)) \<longrightarrow> (snd ((drop i p) ! j) = fst ((drop i p) ! (j + 1)))"
  proof(rule allI)
    fix j
    show "(j + 1 < length (drop i p)) \<longrightarrow> (snd ((drop i p) ! j) = fst ((drop i p) ! (j + 1)))"
    proof(rule impI)
      assume "j + 1 < length (drop i p)"
      also
      have "... = length p - i" by simp
      finally
      have s2:"j + i + 1 < length p" by simp
      hence s1:"(drop i p) ! j = p ! (i + j)" by (simp add:List.nth_drop)
      hence "snd ((drop i p) ! j) = snd (p ! (i + j))" by simp
      also
      from s2 `path G p`  have "... = fst (p ! (i + j + 1))" by (simp add:path_def)
      also
      from s2 have "... = fst((drop i p) ! (j +1))" by (simp add:List.nth_drop)
      finally show "snd (drop i p ! j) = fst (drop i p ! (j + 1))".
    qed
  qed
  from t1 t2 show "path G (drop i p)" by (simp add:path_def)
qed

lemma subPathTake:
  assumes "path G p" 
  shows "path G (take i p)"
using assms proof(cases "i < length p")
  case False
  hence "take i p = p" by simp
  hence "path G p = path G (take i p)" by simp
  with `path G p` show ?thesis by simp
next
  case True
  have "set (take i p) \<subseteq>  set p" by (simp add:List.set_take_subset)
  also
  from `path G p` have "set p \<subseteq> set_of G" by (simp add:path_def)
  finally
  have t1:"set (take i p) \<le> set_of G".
  have t2:"\<forall>j. (j + 1 < length (take i p)) \<longrightarrow> (snd ((take i p) ! j) = fst ((take i p) ! (j + 1)))"
  proof(rule allI)
    fix j
    show "(j + 1 < length (take i p)) \<longrightarrow> (snd ((take i p) ! j) = fst ((take i p) ! (j + 1)))"
    proof(rule impI)
      assume "j + 1 < length (take i p)"
      also
      have "... =  min (length p) i" by simp
      also
      from `i < length p` have "... = i" by simp
      finally
      have s2:"j + 1 < i" by simp
      with `i < length p` have s3:"j + 1< length p" by simp
      from s2 have s1:"(take i p) ! j = p ! j" by (simp add:List.nth_take)
      hence "snd ((take i p) ! j) = snd (p ! j)" by simp
      also
      from s3 `path G p`  have "... = fst (p ! (j + 1))" by (simp add:path_def)
      also
      find_theorems name:List.nth_take
      from s2 have "... = fst((take i p) ! (j + 1))" by (simp add:List.nth_take)
      finally show "snd (take i p ! (j)) = fst (take i p ! (j + 1))".
    qed
  qed
  from t1 t2 show "path G (take i p)" by (simp add:path_def)
qed

lemma pathSplit:
  assumes "path G (p @ q)" "p \<noteq> []" "q \<noteq> []"
  shows "snd (last p) = fst (hd q)"
proof-
    from assms
    have "last p = p ! (length(p) - 1)" by(simp add:List.last_conv_nth)
    also
    from assms
  have h1: "length(p) < length(p @ q)" by(simp)
    from assms have "take(length(p) - 1) p = take(length(p) - 1) (p@q)" by(simp)
    find_theorems "(?p @ ?q) ! ?n"  
    from assms have "length(p) - 1 < length(p)" by(simp)
    hence "p ! (length(p) - 1) = (p @ q) ! (length(p) - 1)" by(simp add:List.nth_append)
  finally have l1:"last p = (p @ q) ! (length(p) - 1)".
    have "q = drop(length(p))(p@q)" by(simp)
    hence "hd q = hd(drop(length(p))(p@q))" by(simp)
    also from `length(p) < length (p@q)`
    have "... = (p@q) ! length(p)" by(rule List.hd_drop_conv_nth)
    also from `p \<noteq> []` have "... = (p@q) ! ((length(p) - 1) + 1)" by(simp)
  finally have l2:"hd q = (p@q) ! ((length(p) - 1) + 1)".
  from l1 have "snd (last p) = snd((p @ q) ! (length(p) - 1))" by(simp)
  also from assms have "snd((p @ q) ! (length(p) - 1)) = fst((p@q) ! ((length(p) - 1) + 1))" by(simp add:path_def)
  also from l2 have "fst((p@q) ! ((length(p) - 1) + 1)) = fst(hd q)" by(simp)
  finally show ?thesis.
qed

lemma pathConnect:
  assumes "path G p" "path G q" "snd (last p) = fst (hd q)"
  shows "path G (p @ q)"
using assms proof(cases "q = []")
  case True
  hence "path G (p @ q) = path G p" by simp
  with assms show "path G (p @ q)" by simp
next
  case False
  from `path G p` `path G q` have "set p \<subseteq> set_of G" "set q \<subseteq> set_of G" by(simp_all add:path_def)
  hence s1:"set (p @ q) \<subseteq> set_of G" by simp
  have "\<forall>i. i + 1 < length (p @ q) \<longrightarrow> snd ((p @ q) ! i) = fst ((p @ q) ! (i + 1))"
  proof(rule allI)
    fix i
    show "i + 1 < length (p @ q) \<longrightarrow> snd ((p @ q) ! i) = fst ((p @ q) ! (i + 1))"
    proof(rule impI)
      assume "i + 1 < length (p @ q)"
      hence "i + 1 < length p + length q" by simp
      show "snd ((p @ q) ! i) = fst ((p @ q) ! (i + 1))"
      proof(cases "i + 1 \<le> length p")
        case True
        show "snd ((p @ q) ! i) = fst ((p @ q) ! (i + 1))"
        proof(cases "i + 1 = length p")
          case True
          hence "i = length p - 1" "length p > 0" "i < length p" by auto
          from `i < length p` have "snd ((p @ q) ! i) = snd (p ! i)" by (simp add:List.nth_append)
          also
          from `i = length p - 1` have "... = snd (p ! (length p - 1))" by simp
          also
          from `length p > 0` have "... = snd (last p)" by (simp add:List.last_conv_nth)
          also
          from assms have "... = fst (hd q)" by simp
          also
          from `q \<noteq> []` have "... = fst (q ! 0)" by (simp add:List.hd_conv_nth)
          also
          have "... = fst ((p @ q) ! (length p))" by (simp add:List.nth_append)
          also
          from True have "... = fst ((p @ q) ! (i + 1))" by simp
          finally show "snd ((p @ q) ! i) = fst ((p @ q) ! (i + 1))".
        next
          from `path G p` have "\<forall>i. i + 1 < length p \<longrightarrow> snd (p ! i) = fst (p ! (i + 1))"
            by (simp add:path_def)
          hence s1:"i + 1 < length p \<longrightarrow> snd (p ! i) = fst (p ! (i + 1))" by (rule allE)
          case False
          with `i + 1 \<le> length p` have "i + 1 < length p" by simp
          hence "i < length p" by simp
          hence "snd((p @ q) ! i) = snd (p ! i)" by (simp add:List.nth_append)
          also
          from `i + 1 < length p` s1 have "... = fst (p ! (i + 1))" by simp
         also
         from `i + 1 < length p` have "... = fst ((p @ q) ! (i + 1))" by (simp add:List.nth_append)
         finally show "snd ((p @ q) ! i) = fst ((p @ q) ! (i + 1))".
        qed
      next
        case False
        hence "i + 1 > length p" by simp
        with `i + 1 < length p + length q` have "i - length p + 1 < length q" by simp
        hence "i - length p < length q" by simp
        from `path G q` have "\<forall>i. i + 1 < length q \<longrightarrow> snd (q ! i) = fst (q ! (i + 1))"
          by (simp add:path_def)
        hence "i - length p + 1 < length q \<longrightarrow> snd (q ! (i - length p)) = fst (q ! (i - length p + 1))"
          by (rule allE)
        with `i - length p + 1 < length q`
        have s1:"snd (q ! (i - length p)) = fst (q ! (i - length p + 1))" by simp
        from `i + 1 > length p` have "\<not> (i < length p)" "\<not> (i + 1 < length p)" by simp_all
        hence "snd((p @ q) ! i) = snd (q ! (i - length p))" by (simp add:List.nth_append)
        also
        from `(i - length p) + 1 < length q` s1 have "... = fst (q ! (i - length p + 1))" by simp
        also
        with `i + 1 > length p` `\<not> (i < length p)`  have "... = fst (q ! (i + 1 - length p))"
          sorry
        also
        from `\<not> (i + 1 < length p)` have "... = fst ((p @ q) ! (i + 1))" by (simp add:List.nth_append)
        finally show "snd ((p @ q) ! i) = fst ((p @ q) ! (i + 1))".
      qed
    qed
  qed
  with s1 show "path G (p @ q)" by (simp add:path_def)
qed

lemma eulerianObtainNext:
  assumes "eulerPath G p" "e \<in># G"
  obtains e' where "e' \<in># G \<and> snd e = fst e'"
using assms
proof-
  from `eulerPath G p` have "path G p \<and> fst (hd p) = snd (last p) \<and> G = multiset_of p"
    by (simp add:eulerPath_def[symmetric])
  hence "path G p" by auto
  assume a1:"\<And>e'. e' \<in># G \<and> snd e = fst e' \<Longrightarrow> thesis"
  from assms have  "e \<in># multiset_of p" by(simp add:eulerPath_def)
  hence "e \<in> set p" by (simp add:in_multiset_in_set)
  hence "\<exists>i < length p.  p!i = e" by (simp add:in_set_conv_nth)
  then obtain i where "i < length p" "p!i = e" by auto
  from `e \<in> set p` have "p \<noteq> []" by auto
  show thesis
  proof(cases "i+1 < length p")
    case False
    with `i < length p` have "i+1 = length p" by auto
    from `p \<noteq> []` have "length p > 0" by auto
    with `i+1 = length p` have "i = length p - 1" by auto
    with `p \<noteq> []` have  "p!i = last p" by (simp add:List.last_conv_nth)
    with `p!i = e` have "e = last p" by auto
    with `eulerPath G p` have s1:"snd e = fst (hd p)" by (simp add:eulerPath_def)
    from `p \<noteq> []` have "hd p = p ! 0" by (rule List.hd_conv_nth)
    with `0 < length p` have "(hd p) \<in># multiset_of p" by (simp add:Multiset.nth_mem_multiset_of)
    with `eulerPath G p` have "(hd p) \<in># G" by(simp add:eulerPath_def)
    with s1 have "(hd p) \<in># G \<and> snd e = fst (hd p)" by simp
    with a1 show thesis.
  next
    case True
    hence "p = take (i + 1) p @ p!(i + 1) # drop (Suc (i + 1)) p" by (rule List.id_take_nth_drop)
    with `path G p` have  s1:"path G (take (i + 1) p @ p!(i + 1) # drop (Suc (i + 1)) p)" by simp
    from `p \<noteq> []` have s2:"take (i + 1) p \<noteq> []" by (simp add:List.take_Suc)
    from True have "p!(i + 1) # drop (Suc (i + 1)) p \<noteq> []" by simp
    with s1 s2 have eq1:"snd (last (take (i + 1) p)) = fst (hd (p!(i + 1) # drop (Suc (i + 1)) p))"
      by (simp add:pathSplit)
    from True have "take (i+1) p = take i p @ [p ! i]" by (simp add:List.take_Suc_conv_app_nth)
    hence "last (take (i + 1) p) = p!(i)" by simp
    with `p!i = e` have eq2:"last (take (i + 1) p) = e"  by simp
    hence "snd e = snd (last (take (i + 1) p))" by simp
    also
    from eq1 have "... = fst (hd (p!(i + 1) # drop (Suc (i + 1)) p))".
    also
    have "... = fst (p!(i + 1))" by simp
    finally have eq3:"snd e = fst (p ! (i + 1))".
    from True have "p ! (i + 1) \<in># multiset_of p" by (simp add:Multiset.nth_mem_multiset_of)
    with `eulerPath G p` have "p ! (i + 1) \<in># G" by (simp add:eulerPath_def)
    with eq3 have "(p ! (i + 1)) \<in># G \<and> snd e = fst (p ! (i + 1))" by simp
    with a1 show thesis.
  qed
qed

lemma eulerianObtainNode:
  assumes "eulerPath G p" "n \<in> (nodes G)"
  obtains e where "e \<in># G \<and> fst e = n"
using assms
proof-
  assume a1:"(\<And>e. e \<in># G \<and> fst e = n \<Longrightarrow> thesis)"
  from `n \<in> (nodes G)` obtain e where "e \<in># G \<and> (fst e = n \<or> snd e = n)" by(rule obtainNode)
  hence "(e \<in># G \<and> fst e = n) \<or> (e \<in># G \<and> snd e = n)" by simp
  thus thesis
  proof(rule disjE)
    assume "e \<in># G \<and> fst e = n"
    with a1 show thesis.
  next
    assume a2:"e \<in># G \<and> snd e = n"
    hence "e \<in># G"..
    with `eulerPath G p` obtain e' where s1:"e' \<in># G \<and> snd e = fst e'" by (rule eulerianObtainNext)
    from a2 have "snd e = n"..
    with s1 have  "e' \<in># G \<and> fst e' = n" by simp
    with a1 show thesis.
  qed
qed

lemma eulerianSplit:
  assumes "eulerPath G p" "n \<in> (nodes G)"
  obtains e where "p = q @ (e # q') \<and> fst e = n"
oops

lemma eulerPathRotate:
  assumes "eulerPath G (p @ q)"
  shows "eulerPath G (q @ p)"
oops

lemma pathFromEulerPath:
  assumes "eulerPath G ep" "m \<in> nodes G" "n \<in> nodes G"
  obtains p where "path G p \<and> (fst (hd p) = n) \<and> (snd (last p) = m)"
using assms proof-
  assume a1:"\<And>p. path G p \<and> fst (hd p) = n \<and> snd (last p) = m \<Longrightarrow> thesis"
  
  from `eulerPath G ep` `n \<in> nodes G`
  obtain en where "en \<in># G \<and> fst en = n" by (rule eulerianObtainNode)
  hence "en \<in># G" "fst en = n" by simp_all
  from `eulerPath G ep` `en \<in># G` have "en \<in># multiset_of ep"
    by (simp add:eulerPath_def)
  hence "en \<in> set ep" by (simp add:Multiset.in_multiset_in_set)
  hence "\<exists>i < length ep. (ep ! i) = en" by (simp add:List.in_set_conv_nth)
  then obtain i where "i < length ep" "ep ! i = en" by auto
  hence "ep \<noteq> []" by auto

  from `eulerPath G ep` `m \<in> nodes G`
  obtain em where "em \<in># G \<and> fst em = m" by (rule eulerianObtainNode)
  hence "em \<in># G" "fst em = m" by simp_all
  from `eulerPath G ep` `em \<in># G` have "em \<in># multiset_of ep"
    by (simp add:eulerPath_def)
  hence "em \<in> set ep" by (simp add:Multiset.in_multiset_in_set)
  hence "\<exists>j < length ep. ep ! j = em" by (simp add:List.in_set_conv_nth)
  then obtain j where "j < length ep" "ep ! j = em" by auto

  from `eulerPath G ep` have "path G ep \<and> fst (hd ep) = snd (last ep) \<and> G = multiset_of ep"
    by (simp add:eulerPath_def[symmetric])
  hence epDefs:"path G ep" "fst (hd ep) = snd (last ep)" by auto
  show thesis
  proof(cases "i \<le> j")
    case True
    show thesis
    proof(cases "i = j")
      case True
      hence "ep ! i = ep ! j" by simp
      with `ep ! i = en` `fst en = n` `fst em = m` `ep ! j = em` 
      have "m = n" by simp
      show thesis
      proof(cases "i = 0")
        case True
        from `ep \<noteq> []` have "fst (hd ep) = fst(ep ! 0)" by (simp add:List.hd_conv_nth)
        also
        with `ep ! i = en` True have "... = fst en" by simp
        also
        with `fst en = n` have "... = n" by simp
        finally have "fst (hd ep) = n".
        from epDefs have "snd (last ep) = fst (hd ep)" by simp
        also
        with `fst (hd ep) = n` have "... = n" by simp
        also
        with `m = n` have "... = m" by simp
        finally have "snd (last ep) = m".
        with `path G ep` `fst (hd ep) = n` a1 show thesis by auto
      next
        case False
        from `i < length ep` have "drop i ep \<noteq> []" by simp
        from `path G ep` have "path G (drop i ep)" by (rule subPathDrop)
        from `path G ep` have "path G (take i ep)" by (rule subPathTake)
     
        from `i < length ep` have "snd (last (drop i ep)) = snd (last ep)" by simp
        also
        from `fst (hd ep) = snd (last ep)` have "... = fst (hd ep)"..
        also
        have "... = fst(hd (take i ep))" sorry
        finally have "snd (last (drop i ep)) = fst (hd (take i ep))".
        from `path G (drop i ep)` `path G (take i ep)` `snd (last (drop i ep)) = fst (hd (take i ep))`
        have s1:"path G ((drop i ep) @ (take i ep))" by(rule pathConnect)
        from `drop i ep \<noteq> []`
        have "fst (hd ((drop i ep) @ (take i ep))) = fst (hd (drop i ep))" by (simp add:List.hd_append2)
        also from `i < length ep` have "... = fst (ep ! i)" by (simp add:List.hd_drop_conv_nth)
        also from `ep ! i = en` have "... = fst en" by simp
        also from `fst en = n` have "... = n" by simp
        finally have s2:"fst (hd (drop i ep @ take i ep)) = n".
        from `i < length ep` have "i mod (length ep) = i" by simp
        hence "fst (last ((drop i ep) @ (take i ep))) = fst (last (rotate i ep))"
          by (simp add:List.rotate_drop_take)

        also from `i < length ep` have "... = fst (ep ! i)"  sorry
        also from `i = j` have "... = fst (ep ! j)" by simp
        also from `ep ! j = em` have "... = fst em" by simp
        also from `fst em = m`  have "...  = m" by simp
        finally have "fst (last (drop i ep @ take i ep)) = m".
        with s1 s2 a1 show thesis by auto
      qed
    next
      case False
      with `i \<le> j` have "i < j"
      
    qed
  qed
qed


theorem eulerian_characterization:  
  "G \<noteq> {#} \<Longrightarrow> eulerian G \<longleftrightarrow> strongly_connected G \<and> (\<forall>v. inDegree G v = outDegree G v)"
proof-
  find_theorems (406) name:Multiset "?b \<in># ?c" "size ?d"
  assume "G \<noteq> {#}"
  hence "size G > 0" by (simp add:Multiset.nonempty_has_size)
  hence "\<exists>n. (size G) = Suc n" by (simp add:gr0_implies_Suc)
  then obtain n where "size G = Suc n" by (rule exE)
  hence "\<exists>e. e \<in># G" by (rule Multiset.size_eq_Suc_imp_elem)
  then obtain e where "e \<in># G" by (rule exE)
  hence nodesNotEmpty:"fst e \<in> (nodes G)" by (simp add:nodes_def)
  show ?thesis
  proof(rule iffI)
    assume "eulerian G"
    with eulerian_def obtain ep where "eulerPath G ep" 
      by auto
    show "strongly_connected G \<and> (\<forall>v. inDegree G v = outDegree G v)"
    proof(rule conjI)
      have " (\<forall>n. n \<in> (nodes G) \<longrightarrow> (\<forall>m. m \<in> (nodes G) \<longrightarrow>
         (\<exists>p. path G p \<and> fst (hd p) = n \<and> snd (last p) = m)))"
      proof(rule allI)
        fix n
        show "n \<in> (nodes G) \<longrightarrow> (\<forall>m. m \<in> (nodes G) \<longrightarrow>
         (\<exists>p. path G p \<and> fst (hd p) = n \<and> snd (last p) = m))"
        proof (rule impI)
          assume niG:"n \<in> (nodes G)"
          show "\<forall>m. m \<in> (nodes G) \<longrightarrow>
            (\<exists>p. path G p \<and> fst (hd p) = n \<and> snd (last p) = m)"
          proof(rule allI)
            fix m
            show "m \<in> (nodes G) \<longrightarrow>
              (\<exists>p. path G p \<and> fst (hd p) = n \<and> snd (last p) = m)"
            proof (rule impI)
              assume miG:"m \<in> (nodes G)"
              show "\<exists>p. path G p \<and> fst (hd p) = n \<and> snd (last p) = m"
              sorry
              from niG obtain e where "e \<in># G \<and> (fst e = n \<or> snd e = n)" by (rule obtain_node)
              sorry
            qed
          qed
        qed
      qed
      thus "strongly_connected G" by(simp add:strongly_connected_def)  
    next
      

      
    qed
  qed
qed

end
