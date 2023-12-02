#include <stdio.h>
#include <stdlib.h>

int main (int argc, char** argv) {
  int size = atoi (argv[1]);
  int magic = size * (size*size + 1) / 2;

  printf ("(set-logic QF_LIA)\n");

  for (int i = 0; i < size; i++)
    for (int j = 0; j < size; j++)
      printf ("(declare-const m_%i_%i Int)\n", i, j);

  for (int i = 0; i < size; i++)
    for (int j = 0; j < size; j++) {
      printf ("(assert (and (> m_%i_%i 0) ", i, j);
      printf ("(<= m_%i_%i %i)))\n", i, j, size*size); }

  for (int i = 0; i < size; i++) {
    printf ("(assert (= %i (+", magic);
    for (int j = 0; j < size; j++)
      printf (" m_%i_%i", i, j);
    printf (")))\n"); }

  for (int i = 0; i < size; i++) {
    printf ("(assert (= %i (+", magic);
    for (int j = 0; j < size; j++)
      printf (" m_%i_%i", j, i);
    printf (")))\n"); }

  printf ("(assert (= %i (+", magic);
  for (int j = 0; j < size; j++)
    printf (" m_%i_%i", j, size - j - 1);
  printf (")))\n");

  printf ("(assert (= %i (+", magic);
  for (int j = 0; j < size; j++)
    printf (" m_%i_%i", size - j - 1, j);
  printf (")))\n");

  printf ("(assert (distinct");
  for (int i = 0; i < size; i++)
    for (int j = 0; j < size; j++)
      printf (" m_%i_%i", i, j);
  printf ("))\n");

  printf ("(check-sat)\n");
  printf ("(get-model)\n");
  printf ("(exit)\n");

}

