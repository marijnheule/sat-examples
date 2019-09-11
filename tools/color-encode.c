#include <stdio.h>
#include <stdlib.h>

int main (int argc, char** argv) {
  FILE* graph  = fopen (argv[1], "r");
  int i, j, a, b, nVertex, nEdge, nColor = atoi  (argv[2]);
  fscanf (graph, " p edge %i %i ", &nVertex, &nEdge);

  printf ("p cnf %i %i\n", nVertex * nColor, nVertex + nEdge * nColor);

  for (i = 0; i < nVertex; i++) {
    for (j = 1; j <= nColor; j++)
      printf ("%i ", i * nColor + j);
    printf ("0\n"); }

  while (1) {
    int tmp = fscanf (graph, " e %i %i ", &a, &b);
    if (tmp == 0 || tmp == EOF) break;
    for (j = 1; j <= nColor; j++)
      printf ("-%i -%i 0\n", (a-1) * nColor + j, (b-1) * nColor + j);
  }
}
