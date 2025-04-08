#include <stdio.h>
#include <stdlib.h>
#include <math.h>

int main (int argc, char** argv) {
  int a, b, c, max, offset = 0, nVars = 0, nClauses = 0;

  if (argc < 2) {
    printf ("run using ./PythagoreanTriples MAX\n"); exit (0); }

  max = atoi (argv[1]);

  for (a = 1; a <= max; a++)
    for (b = a; (a*a + b*b) <= (max * max); b++) {
      c = sqrt(a*a + b*b);
      if ((c*c) == (a*a + b*b)) {
        nClauses += 2;
        if (c > nVars) nVars = c; } }

  printf ("p cnf %i %i\n", nVars, nClauses);

  for (a = 1; a <= max; a++)
    for (b = a; (a*a + b*b) <= (max*max); b++) {
      c = sqrt(a*a + b*b);
      if ((c*c) == (a*a + b*b)) {
        printf (" %i  %i  %i 0\n", a, b, c);
        printf ("-%i -%i -%i 0\n", a, b, c); } }
}
