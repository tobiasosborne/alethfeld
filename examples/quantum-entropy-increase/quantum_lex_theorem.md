# Quantum Entropy Increase Theorem for Lexicographic Boolean Functions

## Module: QuantumLexEntropy

---

### DEFINITION 1 (Pauli Group)

Let $n \in \mathbb{N}$.

1.1. The **single-qubit Pauli matrices** are:
$$I = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}, \quad
X = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}, \quad
Y = \begin{pmatrix} 0 & -i \\ i & 0 \end{pmatrix}, \quad
Z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$$

1.2. The **$n$-qubit Pauli group** $\mathcal{P}_n$ is the set of all $4^n$ operators of the form:
$$P = P_1 \otimes P_2 \otimes \cdots \otimes P_n$$
where each $P_i \in \{I, X, Y, Z\}$.

1.3. For $P \in \mathcal{P}_n$, the **weight** of $P$ is:
$$\mathrm{wt}(P) = |\{i : P_i \neq I\}|$$

---

### DEFINITION 2 (Pauli Expansion)

Let $A$ be a Hermitian operator on $(\mathbb{C}^2)^{\otimes n}$.

2.1. The **Pauli expansion** of $A$ is:
$$A = \sum_{P \in \mathcal{P}_n} \hat{a}(P) \cdot P$$

2.2. The **Pauli coefficients** are:
$$\hat{a}(P) = \frac{1}{2^n} \mathrm{Tr}(P \cdot A)$$

2.3. Note: For Hermitian $A$, all coefficients $\hat{a}(P) \in \mathbb{R}$.

---

### DEFINITION 3 (Pauli Spectral Distribution)

Let $A$ be a Hermitian operator with Pauli expansion $A = \sum_P \hat{a}(P) P$.

3.1. The **squared norm** is:
$$\|A\|_2^2 = \frac{1}{2^n}\mathrm{Tr}(A^2) = \sum_{P \in \mathcal{P}_n} \hat{a}(P)^2$$

3.2. The **Pauli spectral distribution** of $A$ is the probability distribution on $\mathcal{P}_n$ given by:
$$\pi_A(P) = \frac{\hat{a}(P)^2}{\|A\|_2^2}$$

---

### DEFINITION 4 (Spectral Entropy)

Let $A$ be a Hermitian operator with Pauli spectral distribution $\pi_A$.

4.1. The **spectral entropy** of $A$ is:
$$H(A) = -\sum_{P \in \mathcal{P}_n} \pi_A(P) \log_2 \pi_A(P)$$

with the convention $0 \log_2 0 = 0$.

---

### DEFINITION 5 (Quantum Influence)

Let $A$ be a Hermitian operator with Pauli spectral distribution $\pi_A$.

5.1. The **quantum influence** of $A$ is:
$$\mathrm{Inf}(A) = \sum_{P \in \mathcal{P}_n} \mathrm{wt}(P) \cdot \pi_A(P) = \mathbb{E}_{P \sim \pi_A}[\mathrm{wt}(P)]$$

---

### DEFINITION 6 (Classical Boolean Function as Observable)

Let $f: \{0,1\}^n \to \{+1, -1\}$ be a Boolean function.

6.1. The **diagonal observable** associated to $f$ is:
$$L_f = \sum_{x \in \{0,1\}^n} f(x) |x\rangle\langle x|$$

6.2. Note: $L_f$ is Hermitian with eigenvalues $\pm 1$.

---

### DEFINITION 7 (Classical Fourier Expansion)

Let $f: \{0,1\}^n \to \{+1, -1\}$ be a Boolean function.

7.1. For $S \subseteq [n]$, define the **parity function**:
$$\chi_S(x) = (-1)^{\sum_{i \in S} x_i}$$

7.2. The **Fourier expansion** of $f$ is:
$$f(x) = \sum_{S \subseteq [n]} \hat{f}(S) \chi_S(x)$$

7.3. The **Fourier coefficients** are:
$$\hat{f}(S) = \frac{1}{2^n} \sum_{x \in \{0,1\}^n} f(x) \chi_S(x)$$

7.4. **Parseval's identity**: $\sum_S \hat{f}(S)^2 = 1$ for Boolean functions.

---

### DEFINITION 8 (Classical Entropy and Influence)

Let $f: \{0,1\}^n \to \{+1, -1\}$ be a Boolean function.

8.1. The **Fourier entropy** of $f$ is:
$$H(f) = -\sum_{S \subseteq [n]} \hat{f}(S)^2 \log_2 \hat{f}(S)^2$$

8.2. The **total influence** of $f$ is:
$$\mathrm{Inf}(f) = \sum_{S \subseteq [n]} |S| \cdot \hat{f}(S)^2$$

---

### DEFINITION 9 (Lexicographic Boolean Function)

Let $n \in \mathbb{N}$ and $\mu \in (0,1)$.

9.1. The **lexicographic ordering** on $\{0,1\}^n$ is the standard ordering where $x <_{\mathrm{lex}} y$ iff at the first bit position $i$ where $x_i \neq y_i$, we have $x_i = 0$ and $y_i = 1$.

9.2. The **lexicographic Boolean function** $\ell_\mu: \{0,1\}^n \to \{+1,-1\}$ of measure $\mu$ is:
$$\ell_\mu(x) = \begin{cases} +1 & \text{if } \mathrm{rank}_{\mathrm{lex}}(x) < \lfloor \mu \cdot 2^n \rfloor \\ -1 & \text{otherwise} \end{cases}$$

where $\mathrm{rank}_{\mathrm{lex}}(x) \in \{0, 1, \ldots, 2^n - 1\}$ is the position of $x$ in lexicographic order.

9.3. The **lexicographic observable** is $L_\mu = L_{\ell_\mu}$ as in Definition 6.

---

### DEFINITION 10 (Hadamard and T Gates)

10.1. The **Hadamard gate** is:
$$H = \frac{1}{\sqrt{2}} \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$$

10.2. The **T gate** is:
$$T = \begin{pmatrix} 1 & 0 \\ 0 & e^{i\pi/4} \end{pmatrix}$$

10.3. For an operator $A$ on $(\mathbb{C}^2)^{\otimes n}$, define:
$$\mathcal{U}(A) = (T^{\otimes n} H^{\otimes n}) A (T^{\otimes n} H^{\otimes n})^\dagger$$

---

### LEMMA 1 (Diagonal Observable Pauli Expansion)

**Statement**: Let $f: \{0,1\}^n \to \{+1,-1\}$ and let $L_f$ be its diagonal observable. Then:
$$L_f = \sum_{S \subseteq [n]} \hat{f}(S) \cdot Z_S$$
where $Z_S = \bigotimes_{i=1}^n P_i$ with $P_i = Z$ if $i \in S$ and $P_i = I$ otherwise.

**Proof Strategy**:

1.1. Show that $\langle x | Z_S | x \rangle = (-1)^{\sum_{i \in S} x_i} = \chi_S(x)$.

1.2. Verify that $\sum_S \hat{f}(S) Z_S$ has matrix element $\langle x | \cdot | x \rangle = \sum_S \hat{f}(S) \chi_S(x) = f(x)$.

1.3. Confirm off-diagonal elements vanish since $Z_S$ is diagonal. ∎

---

### LEMMA 2 (Hadamard Conjugation of Paulis)

**Statement**: Under conjugation by $H$:
$$H X H^\dagger = Z, \quad H Y H^\dagger = -Y, \quad H Z H^\dagger = X$$

Consequently, for $Z_S = \bigotimes_{i \in S} Z_i \otimes \bigotimes_{i \notin S} I_i$:
$$H^{\otimes n} Z_S (H^{\otimes n})^\dagger = X_S$$

**Proof Strategy**:

2.1. Direct computation of $H X H^\dagger$, $H Y H^\dagger$, $H Z H^\dagger$.

2.2. Apply tensor product structure. ∎

---

### LEMMA 3 (T Gate Conjugation of Paulis)

**Statement**: Under conjugation by $T$:
$$T I T^\dagger = I, \quad T Z T^\dagger = Z$$
$$T X T^\dagger = \frac{1}{\sqrt{2}}(X + Y), \quad T Y T^\dagger = \frac{1}{\sqrt{2}}(Y - X)$$

**Proof Strategy**:

3.1. Direct computation using $T = \mathrm{diag}(1, e^{i\pi/4})$.

3.2. Note that $T X T^\dagger = e^{-i\pi/4} X e^{i\pi/4 \cdot Z}$; expand using $e^{i\theta Z} = \cos\theta \cdot I + i\sin\theta \cdot Z$. ∎

---

### LEMMA 4 (T Conjugation Expansion of X-type Paulis)

**Statement**: Let $S \subseteq [n]$ and let $X_S = \bigotimes_{i \in S} X_i \otimes \bigotimes_{i \notin S} I_i$. Then:
$$T^{\otimes n} X_S (T^{\otimes n})^\dagger = \frac{1}{2^{|S|/2}} \sum_{R \subseteq S} \omega_R \cdot X_{S \setminus R} Y_R I_{S^c}$$

where $\omega_R \in \{1, -1, i, -i\}$ are phases and:
- $X_{S \setminus R} Y_R I_{S^c}$ denotes the Pauli with $X$ at positions $S \setminus R$, $Y$ at positions $R$, and $I$ elsewhere
- All $2^{|S|}$ resulting Paulis have the same weight $|S|$

**Proof Strategy**:

4.1. Apply Lemma 3: each $X_i$ for $i \in S$ maps to $(X_i + Y_i)/\sqrt{2}$.

4.2. Expand the tensor product $\bigotimes_{i \in S} (X_i + Y_i)/\sqrt{2}$.

4.3. Each term in the expansion corresponds to a choice $R \subseteq S$ where position $i$ contributes $Y_i$ iff $i \in R$.

4.4. Track phases from $Y = iXZ$ relations. ∎

---

### LEMMA 5 (Weight Preservation)

**Statement**: Let $A$ be a Hermitian operator and let $U = U_1 \otimes \cdots \otimes U_n$ be a product of single-qubit unitaries. Then:
$$\mathrm{Inf}(U A U^\dagger) = \mathrm{Inf}(A)$$

**Proof Strategy**:

5.1. Single-qubit unitaries map $\{I\} \to \{I\}$ and $\{X, Y, Z\} \to \{X, Y, Z\}$ (up to phases and linear combinations within the set).

5.2. Therefore $\mathrm{wt}(U P U^\dagger)$ involves only Paulis of the same weight as $P$.

5.3. Since the spectral distribution is a probability measure and weight is preserved within its support, influence is invariant.

5.4. Make this precise using Lemma 4: each $X_S$ maps to a uniform combination of Paulis all of weight $|S|$. ∎

---

### LEMMA 6 (Entropy of Uniform Splitting)

**Statement**: Let $\pi$ be a probability distribution on a finite set $\Omega$ with entropy $H(\pi)$. For each $\omega \in \Omega$, let $k_\omega \geq 1$ be an integer. Define a new distribution $\pi'$ on $\Omega' = \bigsqcup_{\omega} \{(\omega, j) : j \in [k_\omega]\}$ by:
$$\pi'(\omega, j) = \frac{\pi(\omega)}{k_\omega}$$

Then:
$$H(\pi') = H(\pi) + \sum_{\omega \in \Omega} \pi(\omega) \log_2 k_\omega$$

**Proof Strategy**:

6.1. Compute directly:
$$H(\pi') = -\sum_{\omega, j} \frac{\pi(\omega)}{k_\omega} \log_2 \frac{\pi(\omega)}{k_\omega}$$

6.2. Separate the logarithm: $\log_2 \frac{\pi(\omega)}{k_\omega} = \log_2 \pi(\omega) - \log_2 k_\omega$.

6.3. Sum over $j$ first (contributing factor $k_\omega$), then over $\omega$.

6.4. Recognize the two resulting sums as $H(\pi)$ and $\mathbb{E}_\pi[\log_2 k_\omega]$. ∎

---

### THEOREM 1 (Quantum Entropy Increase)

**Statement**: Let $f: \{0,1\}^n \to \{+1, -1\}$ be any Boolean function. Let $L_f$ be its diagonal observable and let $\tilde{L}_f = \mathcal{U}(L_f) = T^{\otimes n} H^{\otimes n} L_f H^{\otimes n} (T^{\otimes n})^\dagger$. Then:

$$(i) \quad H(\tilde{L}_f) = H(L_f) + \mathrm{Inf}(L_f) = H(f) + \mathrm{Inf}(f)$$

$$(ii) \quad \mathrm{Inf}(\tilde{L}_f) = \mathrm{Inf}(L_f) = \mathrm{Inf}(f)$$

$$(iii) \quad \frac{H(\tilde{L}_f)}{\mathrm{Inf}(\tilde{L}_f)} = \frac{H(f)}{\mathrm{Inf}(f)} + 1$$

---

**Proof Strategy for Theorem 1**:

**Part (ii)**: Influence invariance.

(ii).1. $H^{\otimes n}$ and $T^{\otimes n}$ are both product unitaries.

(ii).2. Apply Lemma 5 twice.

(ii).3. By Lemma 1, $\mathrm{Inf}(L_f) = \sum_S |S| \hat{f}(S)^2 = \mathrm{Inf}(f)$.

---

**Part (i)**: Entropy increase equals influence.

(i).1. By Lemma 1, $L_f = \sum_S \hat{f}(S) Z_S$.

(i).2. By Lemma 2, $H^{\otimes n} L_f (H^{\otimes n})^\dagger = \sum_S \hat{f}(S) X_S$.

(i).3. The Pauli spectral distribution after $H^{\otimes n}$ is $\pi(X_S) = \hat{f}(S)^2$, unchanged from the original (just relabeled $Z_S \to X_S$). Hence $H(H^{\otimes n} L_f H^{\otimes n \dagger}) = H(L_f)$.

(i).4. By Lemma 4, applying $T^{\otimes n}$ splits each $X_S$ into $2^{|S|}$ Paulis of equal coefficient magnitude.

(i).5. The new Pauli spectral distribution $\pi'$ satisfies the hypotheses of Lemma 6 with $k_S = 2^{|S|}$ (i.e., $k_\omega = 2^{|S|}$ when $\omega$ corresponds to $X_S$).

(i).6. By Lemma 6:
$$H(\tilde{L}_f) = H(L_f) + \sum_S \hat{f}(S)^2 \cdot |S| = H(L_f) + \mathrm{Inf}(f)$$

---

**Part (iii)**: Ratio increase.

(iii).1. Immediate from (i) and (ii):
$$\frac{H(\tilde{L}_f)}{\mathrm{Inf}(\tilde{L}_f)} = \frac{H(f) + \mathrm{Inf}(f)}{\mathrm{Inf}(f)} = \frac{H(f)}{\mathrm{Inf}(f)} + 1$$

∎

---

### COROLLARY 1 (Lower Bound on Quantum FEI Constant)

**Statement**: Suppose the classical Fourier Entropy-Influence conjecture holds with constant $C$, i.e., $H(f) \leq C \cdot \mathrm{Inf}(f)$ for all Boolean functions $f$. Suppose further that the infimum
$$c^* = \sup_f \frac{H(f)}{\mathrm{Inf}(f)}$$
is achieved (or approached) by some sequence of functions. Then the quantum observables $\tilde{L}_f = \mathcal{U}(L_f)$ achieve:
$$\sup_f \frac{H(\tilde{L}_f)}{\mathrm{Inf}(\tilde{L}_f)} \geq c^* + 1$$

In particular, using Hod's lower bound $c^* \geq 6.454784$:
$$\sup_f \frac{H(\tilde{L}_f)}{\mathrm{Inf}(\tilde{L}_f)} \geq 7.454784$$

**Proof Strategy**:

C1.1. Direct application of Theorem 1(iii) to the sequence achieving $c^*$. ∎

---