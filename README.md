# coq_learn

 this project is created in order to learn coq.

# coq library about nat.

 https://coq.inria.fr/library/Coq.Init.Nat.html

# some exercise:

https://github.com/jam231/Software-Foundations
https://github.com/atungare/coq-software-foundations

# reference:

https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html

# notes

1. 等号两边消除，保持格式一致

2. 将格式类似的作为lemma  

3. destruct 也可以用在
   (let (x, y) := h in let (lx, ly) := split t in (x :: lx, y :: ly)) = (l1, l2)
   这样复杂式子中的解耦合。 具体为依次destruct h. destruct (split t).
   
   ## import library:
   
   From Coq Require Import Nat .
   https://www.coder.work/article/6672855
   https://stackoverflow.com/questions/36621752/how-to-import-the-library-coq-arith-peanonat-in-coq

# 一些个人规范

1. assert的sub global 用{}作为bullet
2. induction 和 deduction的bullet等级不要超过2 层。如果一定要超过，考虑lemma。
3. 命名规范
4. 尽可能使用assert，而不是replace.
5. 新的函数definition 或者fixpoint 之后，要加上example 方便阅读。
6. 证明之前先search.
7. 不同抽象等级的变量分别intros.

# tactics:

- intros: move hypotheses/variables from goal to context
- reflexivity: finish the proof (when the goal looks like e = e)
- apply: prove goal using a hypothesis, lemma, or constructor
- apply... in H: apply a hypothesis, lemma, or constructor to a hypothesis in the context (forward reasoning)
- apply... with...: explicitly specify values for variables that cannot be determined by pattern matching
- simpl: simplify computations in the goal
- simpl in H: ... or a hypothesis
- rewrite: use an equality hypothesis (or lemma) to rewrite the goal
- rewrite ... in H: ... or a hypothesis
- symmetry: changes a goal of the form t=u into u=t
- symmetry in H: changes a hypothesis of the form t=u into u=t
- transitivity y: prove a goal x=z by proving two new subgoals, x=y and y=z
- unfold: replace a defined constant by its right-hand side in the goal
- unfold... in H: ... or a hypothesis
- destruct... as...: case analysis on values of inductively defined types
- destruct... eqn:...: specify the name of an equation to be added to the context, recording the result of the case analysis
- induction... as...: induction on values of inductively defined types
- injection... as...: reason by injectivity on equalities between values of inductively defined types
- discriminate: reason by disjointness of constructors on equalities between values of inductively defined types
- assert (H: e) (or assert (e) as H): introduce a "local lemma" e and call it H
- generalize dependent x: move the variable x (and anything else that depends on it) from the context back to an
- explicit hypothesis in the goal formula
- f_equal: change a goal of the form f x = f y into x = y
