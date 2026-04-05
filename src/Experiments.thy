theory Experiments
  imports Main
begin

(*Locale definition of magma as a base theory definition*)
locale magma =
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)

(*Locale definition of semigroup extending magma*)
locale semigroup = magma +
  assumes assoc: "(a \<otimes> b) \<otimes> c = a \<otimes> (b \<otimes> c)"

(*Locale definition of monoid extending semigroup*)
locale monoid = semigroup +
  fixes z :: "'a" ("e")
  assumes left_neutral [simp]: "e \<otimes> a = a"
  assumes right_neutral [simp]: "a \<otimes> e = a" 

(*Locale definition of group extending monoid*)
locale group = monoid +
  fixes inv :: "'a \<Rightarrow> 'a" ("(_\<^sup>-\<^sup>1)" [1000] 999)
  assumes left_inverse [simp]: "inv a \<otimes> a = e"
  assumes right_inverse [simp]: "a \<otimes> inv a = e"

(*Sledgehammered proof of inverse_identity *)
lemma (in group) inv_identity [simp]: "inv e = e"
  by (metis Experiments.group.right_inverse
      Experiments.monoid.left_neutral group_axioms
      monoid_axioms)

end