theory Scratch
  imports Main
begin

type_synonym 'a queue = "'a list"

definition empty :: "'a queue" where
  "empty = []"

definition enqueue :: "'a queue \<Rightarrow> 'a \<Rightarrow> 'a queue" where
  "enqueue q x = q @ [x]"

fun dequeue :: "'a queue \<Rightarrow> ('a queue \<times> 'a)" where
  "dequeue [] = undefined"
| "dequeue (x # xs) = (xs, x)"

definition front :: "'a queue \<Rightarrow> 'a" where
  "front q = snd (dequeue q)"

definition rest :: "'a queue \<Rightarrow> 'a queue" where
  "rest q = fst (dequeue q)"

definition singleton :: "'a \<Rightarrow> 'a queue" where
  "singleton x = enqueue empty x"

lemma dequeue_enqueue_empty:
  "dequeue (enqueue empty x) = (empty, x)"
  unfolding enqueue_def empty_def
  by simp

lemma front_singleton:
  "front (singleton x) = x"
  unfolding front_def singleton_def
  by (simp add: dequeue_enqueue_empty)

lemma rest_singleton:
  "rest (singleton x) = empty"
  unfolding rest_def singleton_def
  by (simp add: dequeue_enqueue_empty)

lemma front_enqueue_nonempty:
  "q \<noteq> empty \<Longrightarrow> front (enqueue q x) = front q"
  unfolding front_def enqueue_def empty_def
  by (cases q) simp_all

lemma rest_enqueue_nonempty:
  "q \<noteq> empty \<Longrightarrow> rest (enqueue q x) = enqueue (rest q) x"
  unfolding rest_def front_def enqueue_def empty_def
  by (cases q) simp_all

end