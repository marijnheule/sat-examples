#include <stdio.h>
#include <stdlib.h>
#include <math.h>

int main (int argc, char** argv) {
  int nVars = 0, nClauses = 0;

  if (argc < 2) {
    printf ("run using ./PythagoreanTriples MAX\n"); exit (0); }

  int max = atoi (argv[1]);

  for (int a = 1; a <= max; a++)
    for (int b = a; (a*a + b*b) <= (max * max); b++) {
      int c = sqrt(a*a + b*b);
      if ((c*c) == (a*a + b*b)) {
        nClauses += 2;
        if (c > nVars) nVars = c; } }

  printf ("p cnf %i %i\n", nVars, nClauses);

  for (int a = 1; a <= max; a++)
    for (int b = a; (a*a + b*b) <= (max*max); b++) {
      int c = sqrt(a*a + b*b);
      if ((c*c) == (a*a + b*b)) {
        printf (" %i  %i  %i 0\n", a, b, c);
        printf ("-%i -%i -%i 0\n", a, b, c); } }
}
