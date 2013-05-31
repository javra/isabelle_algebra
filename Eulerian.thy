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
  where "path G p \<equiv> (multiset_of p \<le> G) \<and> (\<forall>i. (i < length p) \<longrightarrow> (snd (p ! i) = fst (p ! (i + 1))))"

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
  assumes "path G p" "i < length p"
  shows "path G (drop i p)"
using assms proof-
  have "multiset_of (drop i p) \<le> multiset_of p" sorry
  also
  from `path G p` have "multiset_of p \<le> G" by (simp add:path_def)
  finally
  have "multiset_of (drop i p) \<le> G".
  have "\<forall>
  find_theorems Name:path_def
oops

lemma pathSplit:
  assumes "path G (p @ q)" "p \<noteq> []" "q \<noteq> []"
  shows "snd (last p) = fst (hd q)"
proof-
  find_theorems "?p @ ?q = ?r @ ?s"
  have "path G (p @ q) = ((\<exists>e. (p @ q) = [e] \<and> e \<in># G) \<or>
     (\<exists>es1 es2. p @ q = es1 @ es2 \<and> path G es1 \<and> path G es2 \<and> snd (last es1) = fst (hd es2)))"
     by (rule path.simps)
  with `path G (p @ q)`  have "(\<exists>e. (p @ q) = [e] \<and> e \<in># G) \<or>
     (\<exists>es1 es2. p @ q = es1 @ es2 \<and> path G es1 \<and> path G es2 \<and> snd (last es1) = fst (hd es2))"
     by simp
  thus ?thesis
  proof(rule disjE)
    assume a:"\<exists>e. p @ q = [e] \<and> e \<in># G"
    then obtain e where edef:"p @ q = [e]" by auto
    from `p \<noteq> []` `q \<noteq> []` have "length p > 0" "length q > 0" by simp_all
    hence "(length p + length q) > 1" sorry
    hence "length (p @ q) > 1" by simp
    with edef have  "length [e] > 1" by simp
    hence "False" by simp
    thus ?thesis..
  next
    assume a:"\<exists>es1 es2. p @ q = es1 @ es2 \<and> path G es1 \<and> path G es2 \<and> snd (last es1) = fst (hd es2)"
    then obtain p1 p2 where "p @ q = p1 @ p2 \<and> path G p1 \<and> path G p2 \<and> snd (last p1) = fst (hd p2)"
      by auto
    hence "p @ q = p1 @ p2"..
    hence "\<exists>us. p = p1 @ us \<and> us @ q = p2 \<or> p @ us = p1 \<and> q = us @ p2"
      by (simp add:List.append_eq_append_conv2)
    then obtain us where "p = p1 @ us \<and> us @ q = p2 \<or> p @ us = p1 \<and> q = us @ p2"..
    thus ?thesis
    proof(rule disjE)
      assume "p = p1 @ us \<and> us @ q = p2"
      
    qed
  qed
qed
oops

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
    assume "e \<in># G \<and> snd e = n"
    hence "e \<in># G"..
    with `eulerPath G p` have  "e \<in># multiset_of p" by(simp add:eulerPath_def)
    hence "e \<in> set p" by (simp add:in_multiset_in_set)
    hence "\<exists>i < length p.  p!i = e" by (simp add:in_set_conv_nth)
    then obtain i where "p!i = e" by auto
    show thesis
    proof(cases "i + 1 < length p + 1")
      case True
      obtain e' where "e' = p!(i+1)" by auto
      hence "e' \<in> set p" sorry
      hence "e' \<in># multiset_of p" sorry
      with `eulerPath G p` have g1:"e' \<in># G" by (simp add:eulerPath_def)
      have "fst e' = n" sorry
      with g1 have "e' \<in># G \<and> fst e' = n"..
      with a1 show thesis.
    next
      case False
  qed
qed
oops

lemma eulerianSplit:
  assumes "eulerPath G p" "n \<in> (nodes G)"
  obtains e where "p = q @ (e # q') \<and> fst e = n"
sorry

lemma eulerPathRotate:
  assumes "eulerPath G (p @ q)"
  shows "eulerPath G (q @ p)"
sorry


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
