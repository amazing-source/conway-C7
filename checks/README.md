# Exact-arithmetic sanity checks (not part of the proof)

Python 3 with `sympy`; exact rational arithmetic only.

* `residuals.py`: the values of alpha = 12 z_b^2 for every column (Table 1), the square-root triples (Prop. 7.5).
* `census6.py`: all symmetric 6x6 blocks on A u B with entries 0..4, the margins (11), the row bounds from (6)
  and a positive semidefinite Gram block of rank <= 4: 8 classes, the six of Theorem 7.6 and two with h = 6.
* `mixed.py`: for each of the six configurations, all mixed rows (x; y) with a PSD rank <= 4 Gram block on
  A u B u {m}; compares with Section 8 and checks the final row contradiction.

Run: `python census6.py`, `python mixed.py`, `python residuals.py`.
