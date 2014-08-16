
Ex 1
----

a. let n be > m

   Bn ∩ Bm
 = An ∩ An-1^ ∩ ... Am^ ... A1^ ∩ Am ∩ An-2^ ...
 = ∅ ∩ An ∩ An-1^ ∩ An-2^ ...
 = ∅

b. by induction

base:
    A1 = B1 -- def

inductive:
    assume An-1 = ∪i=1,n-1,Bi

   An
 = Bn ∪ An-1 -- lemma
 = Bn ∪ ∪i=1,n-1,Bi -- assumption
 = ∪i=1,n,Bi

lemma:
  Bn = An ∩ An-1^ ∩ ... A1^ -- def
  Bn ∪ An-1 = An ∩ An-1^ ∩ ... A1^ ∪ An-1 -- ∪ An-1 both sides
  Bn ∪ An-1 = An ∩ (An-1^ ∪ An-1) ∩ (An-2^ ∪ An-1) ∩ ... -- dist
  Bn ∪ An-1 = An ∩ Ω ∩ (An-2^ ∪ An-1) ∩ ... -- simp
  Bn ∪ An-1 = An ∩ Ω ∩ Bn-2 ∩ Bn-3 ... -- simp
  Bn ∪ An-1 = An -- simp
 
 :. An = Bn ∪ An-1

Ex 2
----

*theory 2.a* P(∅) = 0

assume:
    P(∅) > 0
    
P(Ω) = 1
P(Ω) + P(∅)= 1 + P(∅) -- + P(∅) both sides
P(Ω ∪ ∅) = 1 + P(∅) -- Ω & ∅  are disjoint, Yolo!
P(Ω ∪ ∅) > 1 -- assumption
P(Ω) > 1 -- simp 

contradiction :. P(∅) = 0

*theory 2.b* A ⊂ B --> P(A) <= P(B)

let: B = A ∪ C, C ∩ A = ∅
P(B) = P(A ∪ C) -- prob int
P(B) = P(A) + P(C) -- 3.
P(B) >= P(A) -- P(C) >= 0 > 0 if C != ∅, 0 if C == ∅

*theory 2.c* 0 <= P(A) <= 1

∅ ⊂ A ⊂ Ω  -- def
0 <= P(A) <= 1 -- by theory 2.a, 2.b and axiom 1

*theory 2.d* P(A^) = 1 - P(A)

Ω = A^ ∪ A -- LEM
P(Ω) = P(A^ ∪ A) -- Prob intro
P(Ω) = P(A^) + P(A) -- since A and A^ are disjoint
1 = P(A^) + P(A) -- 2
1 - P(A^) = P(A)

*theory 2.e* A ∩ B = ∅ ==> P(A ∪ B) = P(A) + P(B)


   P(A ∪ B)
 = P(A ∪ B ∪ ∅ ...) -- since X ∪ ∅  = X
 = P(A) + P(B) + P(∅ ) + ... -- axiom 3
 = P(A) + P(B)


Ex 3
----

a.
Bn = An ∪ An+1 ∪ An+2 ...
Bn+1 = An+1 ∪ An+2 ...

An ∪ An+1 ∪ An+2 ... ⊃ An+1 ∪ An+2 ... 
CLEARLY, Bn ⊃ Bn+1

Cn = An ∩ An+1 ∩ An+2 ...
Cn+1 = An+1 ∩ An+2 ...

An ∩ An+1 ∩ An+2 ... ⊂ An+1 ∩ An+2 ... 
Yolo, Cn ⊂ Cn+1

b.
ω ∈ ∩ n=1,∞Bn

assume:
   there exists an n | ∀ i >= n, ω ∉ Ai.

:. ω ∉ Bn
:. ω ∉ ∩ n=1,∞Bn

ω ∈ ∩ n=1,∞Bn --> ¬(exists n, ∀ i >= n, ω ∉  Ai) -- contrapos
ω ∈ ∩ n=1,∞Bn --> ∀ n, ¬(∀ i |i >= n, ω ∉ Ai)
ω ∈ ∩ n=1,∞Bn --> ∀ n, exists i|i >= n, ω ∈ Ai
ω ∈ ∩ n=1,∞Bn --> ∀ i, ω ∈ Ai -- simp

assume:
   ∀ i|ω ∈ Ai

∀ n ω ∈ Bn, since every Ai st i >= n contains ω
then ω ∈ ∩ n=1,∞Bn

c.
   ω ∈ ∪ n=1,∞Cn
 = exists n | ω ∈ Cn
 = exists n, ∀ i | i >= n, ω ∈ Ai 
 = ∀ i, ω ∈ Ai, except 1 ... n -1 (ie a finite number of them)

Ex 4
----

   (∪,i∈ I,Ai)^
 = {ω∈ Ω ∧ ¬∃ i|i∈ I,ω ∈ Ai} -- def
 = {ω∈ Ω ∧ ∀ i|i∈ I,ω ∈ Ai^}
 = ∩,i∈ I,Ai^ -- def

Ex 5
----

let C = {H,T}
let w1 ... w∞ be members of C
let n ∈ natural numbers
Ω = { ω = (w1, w2 ... wn) ∧ |{wi∈ ω|wi=H}| = 2 }

k-1/2^(k-1)

Ex 6
----

Probility of each element is 1/N, ie 1/∞ = 0.
sum of 0s is 0, but the probability of all events is 1.
Yolo.

Ex 7
----

let Bn = An - (∪i=1,n,An)
Bns are disjoint from Ex1.

   ∪n=1,∞,An  = ∪n=1,∞,Bn -- Ex1.

   P(∪n=1,∞,An)
 = P(∪n=1,∞,Bn) -- Prod int
 = ∑n=1,∞P(Bn) -- 3.

 We know that P(Bn) <= P(An) since Bn ⊂  An
 so P(∪n=1,∞,An) <= ∑n=1,∞P(An)


Ex 8
----

*Lemma*: ∀ i,j | j ≠ i . Ai and Aj are independent

   P(Ai ∩ Aj)
 = 1
 = P(Ai) * P(Aj)

*Proof*:
   P(i=1,∞,∩Ai)
 = A1 * A2 * ... * A∞ -- by independence
 = 1 * 1 * ... * 1
 = 1

Ex 10
-----

   P(win | ¬ switch)
 = P(door 1 after pick) -- only way its possible
 = P(door 1 before pick) -- independence
 = 1/3

   P(win | switch)
 = 1 - P(¬win | switch)
 = 1 - P(door 1)
 = 1 - 1/3
 = 2/3

Ex 11
-----

   P(A^ ∩ B^)
 = P((A ∪ B)^) -- De Morgan
 = 1 - P(A ∪ B) -- complement elim
 = 1 - (P(A) + P(B) - P(A ∩ B)) -- union elim
 = 1 - P(A) - P(B) + P(A ∩ B)
 = 1 - P(A) - P(B) + P(A) * P(B) -- independence of A & B
 = 1 * (1 - P(A)) - P(B) * (1 - P(A))
 = (1 - P(B)) * (1 - P(A))
 = P(B^) * P(A^)

Ex 13
-----

a. Ω = { ω = (w1, w2 ... wn) | (wn = T ∧ w1 = H ... wn-1 = H) ∨ (wn = H ∧ w1 = T ... wn-1 = T) }
b.

i. let X = H1 ∩ H2 ∩ T3, P(X) = 1/8
ii. let Y = T1 ∩ T2 ∩ H3, P(Y) = 1/8

   P((H1 ∩ H2 ∩ T3) ∪ (T1 ∩ T2 ∩ H3))
 = P(X ∪ Y)
 = P(X) + P(Y) - P(X) * P(Y)
 = 0.234375

Ex 14
-----

a. let P(A) = 0

   P(A) * P(X)
 = 0 * P(X)
 = 0

 = P(A ∩ X)
 = 0 -- since A is impossible, A ∩ X is impossible, Yolo

b. let P(A) = 1

   P(A) * P(X)
 = 1 * P(X)
 = P(X)

   P(A ∩ X)
 = P(X) -- simplification, since A is always true, Yolo

c.

P(A ∩ A) = P(A). Since A ∩ A = A.

let P(A) = X

assume:
  X > 0 ∧ X < 1.
P(A) = P(A) * P(A) -- independence
X = X * X
but theres no X | 0 < X < 1 where X = X * X
therefore P(A) = 0 ∨ P(A) = 1


Ex 15
-----

a.
1 is definitely, so P(>= 2 blue of 4).

=  (1/4 * 1/4 * 3/4 * 3/4)
 + (1/4 * 1/4 * 1/4 * 3/4)
 + (1/4 * 1/4 * 1/4 * 1/4)
= 0.05078125

b. same as a, since independent.


Ex 16
-----

1. Rewrite conditional probability:
    P(A|B) = P(A ∩ B) / P(B)
--> P(A ∩ B) = P(A|B) * P(B)

 = P(A ∩ B ∩ C)
 = P(A ∩ (B ∩ C))
 = P(A|(B ∩ C) * P(B ∩ C) -- by 1.
 = P(A|(B ∩ C) * P(B|C) * P(C) -- by 1.

Ex 17
-----

P(A1|B) < P(A1)
P(B) > 0

Assume:
  ∀ i = 2 .. k P(Ai|B) <= P(Ai)

  ∀ i | P(Ai ∩ B) / P(B) < P(Ai)
  TODO
  P(B) == 0
contradiction
  :. P(Ai|B) > P(Ai) for some i = 2 .. k

Ex 18
-----

Windows with Virus:
 = 0.5 * 0.82
 = 0.41

Non Windows with Virus:
 = (0.3 * 0.65) + (0.2 * 0.5)
 = 0.295

Answer:
 = 0.41 / (0.295 + 0.41)
 = 0.5815602836879432











