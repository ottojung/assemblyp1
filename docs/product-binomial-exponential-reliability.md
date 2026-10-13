# Exponential reliability of the MB09 product-binomial score

**Status:** mathematical notes proof; not yet kernel-checked in Lean. Antonina #281 is the formalization target.

## Source and result

Medvedev–Brudno (2009), [Maximum Likelihood Genome Assembly, §6.1, pp. 10–11](https://www.cs.toronto.edu/~brudno/medvedev_MLA.pdf), introduces the exact multinomial global read-count likelihood and then a separable product of binomial marginal scores. The objectives are distinct at finite sample size. We prove a positive reliability theorem for the second objective, without assuming independence of read-type counts.

**Theorem.** Let E be a finite read alphabet with k=|E| at least 2. Let p and q be categorical probability distributions on E, allowing any p_i,q_i in [0,1], including zero or one. Let R_1,...,R_n be iid draws from p, with read-type counts x_i. Define the product-binomial score

$$
B_q(x)=\prod_{i\in E}\binom{n}{x_i}q_i^{x_i}(1-q_i)^{n-x_i}.
$$

Let

$$
h_i(p,q)=\sqrt{p_iq_i}+\sqrt{(1-p_i)(1-q_i)},\qquad
\rho_A(p,q)=\frac1k\sum_{i\in E}h_i(p,q).
$$

If q differs from p, then 0<=rho_A(p,q)<1, and for all n>=0,

$$
\Pr_p[B_q(x)\ge B_p(x)]\le \rho_A(p,q)^n. \tag{1}
$$

With positive prior weights pi_p, pi_q, the MAP comparison satisfies

$$
\Pr_p[\pi_q B_q(x)\ge \pi_p B_p(x)]
\le
\left(\frac{\pi_q}{\pi_p}\right)^{1/(2k)}
\rho_A(p,q)^n. \tag{2}
$$

A union bound yields exponential success against any finite family of alternatives with distinct read distributions.

## Proof

**Step 1 — factor the score over independent READ DRAWS.** Define the contribution of one read of type r by

$$
W_q(r)=q_r\prod_{j\ne r}(1-q_j).
$$

Since x_i counts observations of type i and n-x_i counts observations of types other than i, rearranging finite products gives an exact identity:

$$
B_q(x)=\left(\prod_i\binom{n}{x_i}\right)
\prod_{t=1}^{n}W_q(R_t). \tag{3}
$$

The first factor is candidate-independent. For any r with p_r>0, W_p(r)>0: p_r>0 and every p_j for j≠r is strictly below one. Since true reads lie in that support almost surely,

$$
\frac{B_q(x)}{B_p(x)}
=\prod_{t=1}^n \frac{W_q(R_t)}{W_p(R_t)}.
$$

**Step 2 — factor one-read ratios into Bernoulli terms.** For every category j and read r, define

$$
Z_j(r)=
\begin{cases}
q_j/p_j,&r=j,\\
(1-q_j)/(1-p_j),&r\ne j.
\end{cases}
$$

For the purpose of the proof, define Z_j(r) only for outcomes r in the true support {r:p_r>0}. On that support the denominators displayed above are positive in the selected branch: if r=j then p_j=p_r>0; if r≠j then 1-p_j≥p_r>0. These factors are nonnegative and obey

$$
W_q(r)/W_p(r)=\prod_j Z_j(r).
$$

**Step 3 — elementary AM–GM yields strict moment contraction.** Let alpha=1/(2k). The arithmetic–geometric mean inequality, applied to the k nonnegative numbers sqrt(Z_j(r)), gives pointwise

$$
\left(\frac{W_q(r)}{W_p(r)}\right)^\alpha
=\left(\prod_j\sqrt{Z_j(r)}\right)^{1/k}
\le \frac1k\sum_j\sqrt{Z_j(r)}.
$$

Take expectation over a single categorical read R with law p. By finite-sum interchange and summing over all r other than j (omitting zero-probability outcomes),

$$
\begin{aligned}
\mathbb E_p\left[(W_q(R)/W_p(R))^\alpha\right]
&\le\frac1k\sum_j\mathbb E_p\sqrt{Z_j(R)}\\
&=\frac1k\sum_j
\left(\sqrt{p_jq_j}+\sqrt{(1-p_j)(1-q_j)}\right)\\
&=\rho_A(p,q). \tag{4}
\end{aligned}
$$

By Cauchy–Schwarz, each h_j is at most one: the two vectors
(sqrt(p_j),sqrt(1-p_j)) and (sqrt(q_j),sqrt(1-q_j)) have Euclidean norm one.
Equality holds precisely for p_j=q_j. Since p differs from q, some h_j<1,
and therefore rho_A<1.

**Step 4 — independence across reads and Markov.** Apply Markov to the nonnegative random variable (B_q/B_p)^alpha:

$$
\begin{aligned}
\Pr_p[B_q(x)\ge B_p(x)]
&\le\mathbb E_p[(B_q/B_p)^\alpha]\\
&=\prod_{t=1}^{n}
 \mathbb E_p[(W_q(R_t)/W_p(R_t))^\alpha]\\
&\le\rho_A(p,q)^n.
\end{aligned}
$$

The product in the middle is valid because the R_t are independent.
Now multiply by the constant prior ratio raised to alpha to get (2). QED.

### Sharper alternative

Generalized finite Hölder improves the contraction factor to

$$
\rho_G(p,q)=\left(\prod_i h_i(p,q)\right)^{1/k}
\le\rho_A(p,q)<1.
$$

Indeed, Hölder bounds the expectation of the geometric mean of the sqrt(Z_j)
by the geometric mean of their expectations. The AM–GM result above is the
suggested first Lean target: it uses only finite sums, products, roots, and
the familiar inequalities AM–GM and Cauchy–Schwarz.

## Scope

The statement is for the **product-binomial approximation** from MB09,
not an assertion that it agrees pointwise with the exact multinomial likelihood.
For the exact iid likelihood, the corresponding pairwise Chernoff factor is
the categorical Bhattacharyya affinity sum_i sqrt(p_i q_i).

Read histogram coordinates under a fixed sample size are dependent. This
proof never assumes otherwise; it factors the deterministic score into
functions of independently drawn reads. Neither p nor q needs full support: zero/one coordinates are allowed. All ratios involving p are defined only on p-supported observations; the missing terms in the expectation have probability zero and contribute zero to the displayed affinity. It is unconditional on latent full-start coverage. Equal read distributions cannot distinguish non-equivalent genomes,
so assembly recovery also needs source-faithful genome/read equivalence and
an identifiability theorem. A feasible bidirected flow need not spell one
circular genome unless the appropriate connected-support Eulerian conditions
hold.

## Minimal Lean verification plan

1. Work over a finite nonempty type E and finite samples Fin n -> E;
   prove the deterministic factorization (3).
2. Formalize the pointwise finite AM–GM estimate and expectation (4)
   as finite sums, not a general multinomial measure theory.
3. Prove the Bernoulli affinity inequality by Cauchy–Schwarz, including
   strict equality characterization.
4. Prove the n-fold independent product finite-sum identity and a
   finite Markov bound, then specialize to a finite set of alternatives.

Do not promote this notes proof to a kernel-checked result until a
no-sorry Lean build, axiom audit, independent review, and exact-head CI pass.
