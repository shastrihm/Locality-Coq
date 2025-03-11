# Locality-Coq

### What's inside

`Locality.v` is a Coq script that formalizes and proves a version of Corollary 2 from [this paper](https://arxiv.org/pdf/2007.12159).

**Main Theorem:** The main result we prove is that the point locality of the standard binary encoding  evaluates to a closed form $2^{n} \cdot (2^{n} - 1)$. 

**Background:**
Point locality is a combinatorial property of binary-integer representations. A representation is a mapping from the set of all length $l$ bitstrings to the natural number interval $[0, 2^{l})$.  
Intuitively, point locality tells us to what degree a small change in the binary representation affects the resulting integer representation. More precisely, for a given length $l$, it computes the sum of absolute integer differences (determined by the representation) over all pairs of length $l$ bitstrings that are a single-bit flip away. Refer to Definition 1 in the [paper](https://arxiv.org/pdf/2007.12159) for the mathematical definition of point locality. The definition we use in this Coq script (`Fixpoint point_locality`) is slightly modified to wave away the terms not dependent on the representation, but the results are equivalent). 


In this formalization, we focus on the point locality of standard binary, proving the following theorem statement:

```
Theorem point_locality_closed_form_standard_binary :
    forall (n : nat),
        n > 0 -> 
            point_locality (standard_bin_to_nat) (all_bitstrings_of_length_n n) 
            = (exp 2 n) * ((exp 2 n) - 1).
```

**Intermediate results:**
As part of building up the machinery to prove the main result, we've included a number of relatively lightweight formalisms. These include:
- Miscellaneous properties for natural numbers (these are relatively trivial)
- Definition and properties for absolute differences ($|a - b|$).
- Definition and properties of exponentiation
- Formalizing single-bit flips
- Formalizing standard binary encoding
- Formalism and correctness lemmas for the enumeration of all length $l$ bitstrings
- Formalizing inner point locality (for a single bitstring) and point locality (inner point locality summed over all possible length l bitstrings)

From here, the series of intermediate helper theorems/lemmas that bring us to the main result are
- Lemmas for absolute differences between single bit-flipped bitstrings in standard binary
- Equivalence between inner point locality and sum of powers of 2
- Theorem for closed form for inner point locality
- Lemma showing point locality for standard binary is only dependent on the length of the bitstrings

**Code from External sources:**
Apart from the Coq standard library, the only external code we include in `Locality.v` are `All` and `All_In` from the [Logic chapter of Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html).



### How to Run
This was developed with Coq version `8.18.0`.
The only dependencies are from Coq's standard library -- basic machinery to reason with bools, nats, and lists. 
To run this:

- Download this repo and follow the instructions to install and run [vscoq](https://github.com/coq/vscoq).

- Alternatively, you can easily run this on the browser by pasting `Locality.v` in [jscoq](https://coq.vercel.app/scratchpad.html).



