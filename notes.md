## 2023.2.27

- 枚举类型
```coq
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
```
Inductive: 归纳数据类型

- 声明函数 
```coq
Definition next_weekday (d:day) : day :=
  match d with
  | monday ⇒ tuesday
  | tuesday ⇒ wednesday
  | wednesday ⇒ thursday
  | thursday ⇒ friday
  | friday ⇒ monday
  | saturday ⇒ monday
  | sunday ⇒ monday
  end.
```
- 具有类型推导能力(两个day可省略)
- 基于空格的函数调用
  - 左结合`f a b`=>`(f a) b`. `f a`返回以b为参数的函数.
  - 空格优先级通常大于其它操作.
- 定理与证明
```coq
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.
```
- Example声明定理
- simpl.化简
- reflexivity.根据对称性


- Bool

```coq
Inductive bool : Type :=
  | true
  | false.


Definition negb (b:bool) : bool :=
  match b with
  | true ⇒ false
  | false ⇒ true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ b2
  | false ⇒ false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ true
  | false ⇒ b2
  end.
```
- 语法定义支持
```coq
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
```

- If条件
```coq
Definition negb' (b:bool) : bool :=
  if b then false
  else true.
Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.
```
- if可以使用任意包含两个"构造函数"的类型, 其中第一个使用then.


- check

`Check orb: bool -> bool
-> bool`
- ->右结合

- 带参构造
```coq
Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).
```

- Modules

```coq
Module Playground.
  Definition b : rgb := blue.
End Playground.
Definition b : bool := true.
Check Playground.b : rgb.
Check b : bool.
```
类似于namespace

- Tuples
```coq
Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0)
  : nybble.
```
- 自然数
```coq
Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
  match n with
  | O ⇒ O
  | S n' ⇒ n'
  end.

Definition minustwo (n : nat) : nat :=
  match n with
  | O ⇒ O
  | S O ⇒ O
  | S (S n') ⇒ n'
  end.
```
标准库中已有定义
```coq
Check (S (S (S (S O)))).
(* ===> 4 : nat *)
```
- 计算过程: 在表达式上进行匹配与变换 `minustwo (S (S n)) = n`
- 递归
```coq
Fixpoint even (n:nat) : bool :=
  match n with
  | O ⇒ true
  | S O ⇒ false
  | S (S n') ⇒ even n'
  end.
```
- Fixpoint

```coq
Fixpoint plus (n:nat) (m:nat) : nat :=
	match n with
	| O => m
	| S n' => S (plus n' m)
	end.

Fixpoint mult (n m:nat) : nat :=
	match n with 
	| O => O
	| S n' => plus m (mult n' m)
	end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ ⇒ O
  | S _ , O ⇒ n
  | S n', S m' ⇒ minus n' m'
  end.
```

- Structrual Recursion
  - Coq: 递归必须终止
  - 结构递归: 实参是原形参的子结构

- 比较
```coq
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O ⇒ match m with
         | O ⇒ true
         | S m' ⇒ false
         end
  | S n' ⇒ match m with
            | O ⇒ false
            | S m' ⇒ eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O ⇒ true
  | S n' ⇒
      match m with
      | O ⇒ false
      | S m' ⇒ leb n' m'
      end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
```


```coq
Theorem plus_O_n : ∀ n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.
```
- 全称量词
  - intros n或intros: 将n移入假设区域.

```coq
Theorem plus_id_example : ∀ n m:nat,
  n = m →
  n + n = m + m.

Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite → H.
  reflexivity. Qed.
```
- rewrite: 将H的左边替换成右边, 箭头默认朝右.

```coq
Theorem plus_1_neq_0_firsttry : ∀ n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl. (* does nothing! *)
Abort.

Theorem plus_1_neq_0 : ∀ n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.
```
- 分类讨论destruct: 按类型的归纳定义分类
  - `as [| n']`: 给定义参数取名
  - `eqn:E`: 保留destruct带来的等价关系.
  - `-` 表示两种case的证明, 可使用-,+,*重复一次或多次, 或者{}

## 2023.3.2

```coq
Theorem add_0_r_firsttry : ∀ n:nat,
  n + 0 = n.
```

- 结构归纳法
  - 对递归定义的类型
  - 证明命题P对类型的每一个构造函数均成立.
    - 若构造函数接受该类型的参数, 则假设P对参数成立.
```coq
Theorem add_0_r : ∀ n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' 
   * n': nat
   * IHn' : n' + 0 = n
   * ================
   * S n' + 0 = S n'
   *) simpl. rewrite → IHn'.(* apply Ihn' *) reflexivity. Qed.
```

```coq
Theorem mult_0_plus' : ∀ n m : nat,
  (n + 0 + 0) × m = n × m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite → H.
  reflexivity. Qed.
```

- assert可以重定位rewrite
```coq
Theorem plus_rearrange : ∀ n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. Qed.
```

- Pair
```coq
Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y ⇒ x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y ⇒ y
  end.

```

- List
```coq
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
```
- `1+x::l` == `(1+x)::l`

```coq
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O ⇒ nil
  | S count' ⇒ n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil ⇒ O
  | h :: t ⇒ S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil ⇒ l2
  | h :: t ⇒ h :: (app t l2)
  end.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil ⇒ default
  | h :: t ⇒ h
  end.
Definition tl (l : natlist) : natlist :=
  match l with
  | nil ⇒ nil
  | h :: t ⇒ t
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
```

```coq
Theorem app_assoc : ∀ l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite → IHl1'. reflexivity. Qed.
```

- search定理

  - 按名称搜索`Search rev`
  - 按形式搜索`Search (_ + _ = _ + _)`
    - 限定`Search (_ + _ = _ + _) inside Induction`
  - 按变量模式匹配 `Search ?x + ?y = ?y + ?x)`

- Options
```coq
Inductive natoption : Type :=
  | Some (n : nat)
  | None.
```
- 处理例外

```coq
Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil ⇒ None
  | a :: l' ⇒ match n with
               | O ⇒ Some a
               | S n' ⇒ nth_error l' n'
               end
  end.
```

- Partial Map
```coq
Inductive id : Type :=
  | Id (n : nat).

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

  Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 ⇒ n1 =? n2
  end.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty ⇒ None
  | record y v d' ⇒ if eqb_id x y
                     then Some v
                     else find x d'
  end.
```

- Polymorphism
  - Ad-Hoc: overloads
    - Coq中对不同的函数定义相同的符号
  - Parametric(*): 同一个函数/类型的定义对多个类型都适用.
    - 面向对象: 泛型
  - Subtyping
    - 不同子类的成员函数表现不同的类型.
```coq
Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list : Type → Type.

Check nil : ∀ X : Type, list X.

Check (nil nat) : list nat.

Check cons : ∀ X : Type, X → list X → list X.
```

- 多态函数
```coq
Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 ⇒ nil X
  | S count' ⇒ cons X x (repeat X x count')
  end.
```



