
### Definition 1 $Injective$

Let $X$ and $Y$ be sets and $f : X \to Y$ a map. The map $f$ is **injective** if

$$
\forall x_1, x_2 \in X, \quad f(x_1) = f(x_2)  \implies x_1 = x_2
$$

---

### Definition 2 $Surjective$

Let $X$ and $Y$ be sets and $f : X \to Y$ a map. The map $f$ is **surjective** if

$$
\forall y \in Y, \ \exists x \in X \text{ such that } f(x) = y
$$

---

### Definition 3 $Bijective$

Let $X$ and $Y$ be sets and $f : X \to Y$ a map. The map $f$ is **bijective** if it is both injective and surjective:

$$
f \text{ is bijective } \iff f \text{ is injective } \wedge f \text{ is surjective.}
$$

---

## Proposition 1 — Basic Properties

Let $X$ and $Y$ be sets and $f : X \to Y$ a map. Then:

1. If $f$ is bijective, then $f$ is injective.
2. If $f$ is bijective, then $f$ is surjective.
3. If $f$ is surjective and injective, then $f$ is bijective.

**Proof:**

1. Let $f$ be bijective, i.e., injective and surjective. Then $f$ is injective by elimination of the conjunction.
2. Similarly, $f$ is surjective by elimination of the conjunction.
3. If $f$ is surjective and injective, then $f$ satisfies both properties, hence by definition it is bijective.

---

## Proposition 2 — Composition Properties

Let $X, Y, Z$ be sets and let $f : X \to Y$, $g : Y \to Z$ be maps. Then:

1. If $g \circ f$ is injective, then $f$ is injective.
2. If $g \circ f$ is surjective, then $g$ is surjective.

**Proof:**

1. Let $x_1, x_2 \in X$ such that $f$x_1$ = f$x_2$$. Then

$$
g(f(x_1)) = g(f(x_2))
$$

Since $g \circ f$ is injective, it follows that $x_1 = x_2$. Hence $f$ is injective.

2. Let $z \in Z$. Since $g \circ f$ is surjective, there exists $x \in X$ such that

$$
g(f(x))= z
$$

Let $y := f$x$ \in Y$. Then

$$
g(y) = g(f(x)) = z
$$

Hence $g$ is surjective.

---

## Corollary 1 — Square Map Property

Let $X$ be a set and $f : X \to X$ such that $f \circ f$ is bijective. Then $f$ is bijective.

**Proof:**

* **Injective:** Since $f \circ f$ is injective, Proposition 1.4.6 $part 1$ shows $f$ is injective.
* **Surjective:** Since $f \circ f$ is surjective, Proposition 1.4.6 $part 2$ shows $f$ is surjective.
* **Conclusion:** $f$ is both injective and surjective, hence bijective.

---

## Example 1 — Neither Injective Nor Surjective

Consider the map $f : {1,2,3} \to {1,2,3}$ defined by

$$
f(1)= 1, \quad f(2) = 1, \quad f(3) = 2
$$

* **Not injective:** $f(1) = f(2)$ but $1 \neq 2$
* **Not surjective:** $3 \notin \text{Im}f$

---

## Example 2 — Bijective Map

Consider the map $g : {1,2} \to {1,2}$ defined by

$$
g(1)= 2, \quad g(2) = 1
$$

* **Injective:** Each element of the domain maps to a unique element in the codomain.
* **Surjective:** Every element of the codomain has a preimage.
* **Conclusion:** $g$ is bijective.
