# schonhage-strassen-in-lean
Machine verification of Schonhage-Strassen FFT multiplication, assisted by Aristotle @Aristotle-Harmonic and Claude Opus 4.6.

We prove $\forall 2 \leq k < (\lg n)$ where $2^k | n$, and $\forall n'$ s.t. $2M + k \leq n' < n$. This accounts for virtually the full acceptable range of $k$ and $n'$.
