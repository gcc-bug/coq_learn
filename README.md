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
   
   ## import library:
   
   From Coq Require Import Nat .
   https://www.coder.work/article/6672855
   https://stackoverflow.com/questions/36621752/how-to-import-the-library-coq-arith-peanonat-in-coq

# 一些个人规范
1. assert的sub global 用{}作为bullet
2. induction 和 deduction的bullet等级不要超过2 层。如果一定要超过，考虑lemma。
3. 