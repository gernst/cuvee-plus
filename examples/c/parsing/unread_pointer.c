// ./Cuvee.sh -verify -z3 examples/c/parsing/unread_pointer.c
// local pointers that are never read, to which arrays are assigned, as in SV-COMP
// loops/veris.c_sendmail_tTflag_arr_one_loop: their assignments are dropped, since only allocations are arrays
int main(void) { char in[3]; char *s; in[0] = 1; s = in; char *t = in; assert(in[0] == 1); return 0; }
