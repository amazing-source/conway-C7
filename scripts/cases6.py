"""The six A/B-block configurations, in the labelling used in the write-up
(P = Q and R = R^T in every case).  Indices 0,1,2 = a1,a2,a3; 3,4,5 = b1,b2,b3."""

def sym(P, Q, R):
    C6 = [[0] * 6 for _ in range(6)]
    for i in range(3):
        for j in range(3):
            C6[i][j] = P[i][j]; C6[3 + i][3 + j] = Q[i][j]
            C6[i][3 + j] = R[i][j]; C6[3 + j][i] = R[i][j]
    return C6

T111 = [[0, 1, 1], [1, 0, 1], [1, 1, 0]]
T112 = [[0, 1, 1], [1, 0, 2], [1, 2, 0]]
T113 = [[0, 1, 1], [1, 0, 3], [1, 3, 0]]
T122 = [[0, 1, 2], [1, 0, 2], [2, 2, 0]]
PQR = {
    1: (T111, [[2, 0, 0], [0, 2, 0], [0, 0, 2]]),
    2: (T111, [[2, 0, 0], [0, 1, 1], [0, 1, 1]]),
    3: (T111, T111),
    4: (T112, T112),
    5: (T113, [[0, 1, 1], [1, 1, 2], [1, 2, 1]]),
    6: (T122, [[0, 1, 2], [1, 2, 0], [2, 0, 2]]),
}
CASES = {k: sym(P, P, R) for k, (P, R) in PQR.items()}
