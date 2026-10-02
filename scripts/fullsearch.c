/* Independent brute-force cross-check (no Gram/PSD reasoning):
 * search all symmetric 12x12 matrices C with entries 0..4, prescribed diagonal D,
 * u = (1,1,1,-1,-1,-1,0,...,0), satisfying
 *   C 1 = 12 1,  C u = 0,  C^2 + C = 12 I + 12 J - 2 u u^T.
 * Usage: fullsearch d0 d1 ... d11   (diagonal entries; default all 0)
 * Prints the number of solutions found (stops after 5 printed).
 */
#include <stdio.h>
#include <stdlib.h>
#define N 12
static int C[N][N], D[N], u[N] = {1,1,1,-1,-1,-1,0,0,0,0,0,0};
static int rs[N], rq[N], ru[N];          /* partial row sum, square sum, u-sum */
static int tq[N];                        /* target square sum */
static long long nodes = 0, sols = 0;
static int nfree[N];                     /* free entries remaining in row */

static int feasible(int r) {
  int s = 12 - rs[r], q = tq[r] - rq[r], f = nfree[r];
  if (s < 0 || q < 0) return 0;
  if (s > 4 * f) return 0;
  if (q < s || q > 4 * s) return 0;
  /* u-residual: entries left with u=+1 / -1 bounded by s */
  int ures = -ru[r];  /* need sum of remaining x_j u_j = ures */
  if (ures > s || -ures > s) return 0;
  /* sum of squares at least s^2/f */
  if (f > 0 && (long long)q * f < (long long)s * s) return 0;
  if (f == 0 && (s != 0 || q != 0 || ures != 0)) return 0;
  return 1;
}

static int rowcheck(int i) {
  for (int p = 0; p < i; p++) {
    int d = 0;
    for (int k = 0; k < N; k++) d += C[i][k] * C[p][k];
    if (d + C[i][p] != 12 - 2 * u[i] * u[p]) return 0;
  }
  return 1;
}

static void rec(int i, int j) {
  nodes++;
  if (j == N) {
    if (!rowcheck(i)) return;
    if (i == N - 2) {
      /* last row is fully determined; check it too */
      if (!feasible(N - 1) || !rowcheck(N - 1)) return;
      sols++;
      if (sols <= 5) {
        printf("SOLUTION\n");
        for (int a = 0; a < N; a++) { for (int b = 0; b < N; b++) printf("%d ", C[a][b]); printf("\n"); }
        fflush(stdout);
      }
      return;
    }
    rec(i + 1, i + 2);
    return;
  }
  for (int x = 0; x <= 4; x++) {
    C[i][j] = C[j][i] = x;
    rs[i] += x; rq[i] += x * x; ru[i] += x * u[j]; nfree[i]--;
    rs[j] += x; rq[j] += x * x; ru[j] += x * u[i]; nfree[j]--;
    if (feasible(i) && feasible(j)) rec(i, j + 1);
    rs[i] -= x; rq[i] -= x * x; ru[i] -= x * u[j]; nfree[i]++;
    rs[j] -= x; rq[j] -= x * x; ru[j] -= x * u[i]; nfree[j]++;
    C[i][j] = C[j][i] = 0;
  }
}

int main(int argc, char **argv) {
  for (int i = 0; i < N; i++) D[i] = (argc > 1 + i) ? atoi(argv[1 + i]) : 0;
  for (int i = 0; i < N; i++) {
    C[i][i] = D[i];
    rs[i] = D[i]; rq[i] = D[i] * D[i]; ru[i] = D[i] * u[i];
    nfree[i] = N - 1;
    tq[i] = 24 - 2 * u[i] * u[i] - D[i]; /* sum_j C_ij^2 (incl. diagonal) = 24 - 2u_i^2 - C_ii */
  }
  rec(0, 1);
  printf("diag:"); for (int i = 0; i < N; i++) printf(" %d", D[i]);
  printf("  solutions=%lld nodes=%lld\n", sols, nodes);
  return 0;
}
