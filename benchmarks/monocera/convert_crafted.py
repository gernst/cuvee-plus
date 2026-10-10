import os
import re


max_files = ["sanfoundry_27_ground.c", "standard_vararg_ground.c", "battery_diag.c", "new_battery_diag.c", "max_eq.c" ,"max_leq.c", "standard_maxInArray_ground.c"]
sum_files = ["brs5.c", "conda.c", "ms1.c", "ms5.c", "s1lif.c", "two_arrays_sum.c", "new_two_arrays_sum.c"]

svcomp_files = ["brs5.c", "conda.c", "ms1.c", "ms5.c", "s1lif.c", "sanfoundry_27_ground.c", "standard_vararg_ground.c", "standard_maxInArray_ground.c"]

sum_loop = """
  int sum = 0;
  for (int i = 0; i < N; i++) {
    sum += arr2[i];
  }
  assert(sum >= 0);
"""

file_dict = {"sum_geq.c":"sum", "two_arrays_sum.c":"sum", "min_eq.c":"min", "min_geq.c":"min", "max_eq.c":"max", "forall1.c":"forall", "battery_diag.c":"max", "max_leq.c":"max", "sum_eq.c":"sum"}

def write_three_files(f10, f100, fub, fname, tool):
    # if fname in max_files: destdir = dir+"/max_tests/"
    # elif fname in sum_files: destdir = dir+"/sum_tests/"
    # else: assert(false)
    #
    #
    # if fname in svcomp_files:
    #     fname = "sv-" + fname

    for testdir in ["polished_tests"]:   #, "polished_tests_nomalloc"]:
        destdir = testdir+"/"+tool+"/"+file_dict[fname]+"/" #+"/crafted_tests/"
        if not os.path.exists(destdir):
            os.makedirs(destdir)

        with open(destdir+fname[:len(fname)-2]+"-10.c", 'w') as f:
            f.write(f10)
        with open(destdir+fname[:len(fname)-2]+"-100.c", 'w') as f:
            f.write(f100)
        if fname == "battery_diag.c": # battery file cannot be unbounded since array is in struct
            return
        with open(destdir+fname[:len(fname)-2]+"-UB.c", 'w') as f:
            f.write(fub)

def sv_to_seahorn(s, fname):
    sea = s.replace("void __VERIFIER_assert", "//void __VERIFIER_assertWASHERE")
    sea = sea.replace('__VERIFIER_assert(', 'sassert(')
    sea = sea.replace("assume_abort_if_not(N", "assume(N")
    sea =  "#include<seahorn/seahorn.h>\n\n" + sea
    sea = sea.replace("sum[0]", "sum")
    sea = sea.replace("sum[1]", "sum")
    sea = sea.replace("sum[1]", "sum")
    sea = sea.replace("long long", "int")
    sea10 = sea.replace("100000", "10")
    sea10 = sea10.replace("N <= 2147483647/sizeof(int)", "N == 10")
    sea100 = sea10.replace("10", "100")
    seaUB = sea10.replace("N == 10", "N > 0")
    seaUB = seaUB.replace("SIZE == 10", "SIZE > 0")

    write_three_files(sea10, sea100, seaUB, fname, "seahorn")


def get_max_loop(a, N, cmp):
    s =   """
  int max = {0}[0];
  for (int i = 0; i < {1}; i++) {{
      if ({0}[i] > max) {{
          max = {0}[i];
      }}
  }}
  assert(max {2});""".format(a,N, cmp)
    return s
def get_min_loop(a, N, cmp):
    s =   """
  int min = {0}[0];
  for (int i = 0; i < {1}; i++) {{
      if ({0}[i] < min) {{
          min = {0}[i];
      }}
  }}
  assert(min {2});""".format(a,N, cmp)
    return s
def get_sum_loop(a, N, cmp):
    s =   """
  int sum = 0;
  for (int i = 0; i < {1}; i++) {{
      sum += {0}[i];
  }}
  assert(sum {2});""".format(a, N, cmp)
    return s

def get_max_assumes(asm_str):
    s = """
  int k = __VERIFIER_nondet_int();
  {0}(0 <= k && k < N);
  assert(arr[k] <= N-1);
  """.format(asm_str)
    return s
     # // assert(\max(arr, 0, N) <= N);

def get_cpa_defs():
    s = """
void reach_error(){};

void __VERIFIER_assume(int cond) {
  if (!cond) {
    while (1) {};
  }
}

void __VERIFIER_assert(int cond) {
  if (!cond) {
    reach_error();
  }
}
    """
    return s

exist_loop = """
  int b = 0;
  for (int j = 0; j < N; j++) {
    if (arr [j] < 3-N) {b = 1;}
  }
  assert(b == 1);
"""
forall_loop = """
  for (int j = 0; j < N; j++) {
    assert(arr[j] == (j*j*j*j));
  }
"""

def ours_to_seahorn(s, fname):
    sea =  "#include<seahorn/seahorn.h>\n\n" + s

    forall_stmt = "//@ assert \\forall int j; ((0 <= j) && (j < N)) ==> (arr[j] == (j*j*j*j));"
    exist_stmt = "//@ assert \exists int j; ((0 <= j) && (j < N)) && (arr[j] < (3-N));"
    sea = sea.replace(forall_stmt, forall_stmt.replace("@", "") + "\n" + forall_loop)
    sea = sea.replace(exist_stmt, exist_stmt.replace("@", "") + "\n" + exist_loop)
    sea = replace_min_max_sum(sea)
    sea = sea.replace("assert(bpack.max_voltage == \max(bpack.batt_voltages, 0, 10));",
                        get_max_loop("bpack.batt_voltages", "10", " == bpack.max_voltage"))
    sea = sea.replace("//@ assert \exists int j; ((0 <= j) && (j < N)) && (arr[j] < (3-N));", exist_loop)
    sea = sea.replace("//@ assert \forall int j; ((0 <= j) && (j < N)) ==> (arr[j] == (j*j*j*j));", forall_loop)
    sea = sea.replace("assert(", "sassert(")

    sea10 = sea
    sea100 = sea10.replace("10", "100")
    s = """
  int N = __VERIFIER_nondet_int();
  assume(N > 0);
  """
    seaUB = sea10.replace("int N = 10;", s)

    dir = "seahorn"
    write_three_files(sea10, sea100, seaUB, fname, dir)


def sv_to_cpa(s, fname):
    asm_s = """
void __VERIFIER_assume(int cond) {
  if (!cond) {
    while (1) {};
  }
}
    """
    cpa = s.replace("sum[0]", "sum")
    cpa = cpa.replace("sum[1]", "sum")
    cpa = cpa.replace("sum[1]", "sum")
    cpa = cpa.replace("long long", "int")
    cpa = cpa.replace("assume(", "__VERIFIER_assume(")
    cpa = asm_s + cpa

    cpa10 = cpa.replace("100000", "10")
    cpa10 = cpa10.replace("N <= 2147483647/sizeof(int)", "N == 10")
    cpa100 = cpa10.replace("10", "100")
    cpaUB = cpa10.replace("N == 10", "N > 0")
    cpaUB = cpaUB.replace("SIZE == 10", "SIZE > 0")



    write_three_files(cpa10, cpa100, cpaUB, fname, "cpa")

def ours_to_cpa(s, fname):
    forall_stmt = "//@ assert \\forall int j; ((0 <= j) && (j < N)) ==> (arr[j] == (j*j*j*j));"
    exist_stmt = "//@ assert \exists int j; ((0 <= j) && (j < N)) && (arr[j] < (3-N));"
    cpa = s.replace(forall_stmt, forall_stmt.replace("@", "") + "\n" + forall_loop)
    cpa = cpa.replace(exist_stmt, exist_stmt.replace("@", "") + "\n" + exist_loop)
    cpa = replace_min_max_sum(cpa)
    cpa = cpa.replace("assert(bpack.max_voltage == \max(bpack.batt_voltages, 0, 10));",
                        get_max_loop("bpack.batt_voltages", "10", " == bpack.max_voltage"))
    cpa = cpa.replace("assert(", "__VERIFIER_assert(")
    cpa = get_cpa_defs() + cpa

    cpa10 = cpa
    cpa100 = cpa10.replace("10", "100")
    s = """
  int N = __VERIFIER_nondet_int();
  __VERIFIER_assume(N > 0);
  """
    cpaUB = cpa10.replace("int N = 10;", s)

    dir = "cpa"
    write_three_files(cpa10, cpa100, cpaUB, fname, dir)

def sv_to_monocera(s, fname):
    mono = s.replace("assume_abort_if_not", "assume")
    mono = mono.replace("long long sum[1];", "//long long sum[1];")
    mono = mono.replace("int sum[1];", "//int sum[1];")
    mono = mono.replace("sum[0] = 0", "//sum[0] = 0")
    mono = mono.replace("long long", "int")
    mono = mono.replace("*a = malloc", "a[] = malloc")
    mono = mono.replace("extern void", "//extern void")
    mono10 = mono.replace("100000", "10")
    mono10 = mono10.replace("N <= 2147483647/sizeof(int)", "N == 10")
    mono100 = mono10.replace("10", "100")
    monoUB = mono10.replace("N == 10", "N > 0")
    monoUB = monoUB.replace("SIZE == 10", "SIZE > 0")

    write_three_files(mono10, mono100, monoUB, fname, "monocera")

def ours_to_monocera(s, fname):
    mono10 = s
    mono100 = mono10.replace("10", "100")
    s = """
  int N = __VERIFIER_nondet_int();
  __VERIFIER_assume(N > 0);
  """
    monoUB = mono10.replace("int N = 10;", s)

    dir = "monocera"
    write_three_files(mono10, mono100, monoUB, fname, dir)

def sv_to_tricera(s, fname):
    tri = s.replace("sum[0]", "sum")
    tri = tri.replace("sum[1]", "sum")
    tri = tri.replace("sum[1]", "sum")
    tri = tri.replace("long long", "int")
    tri = tri.replace("extern void", "//extern void")
    tri = tri.replace("*a = malloc", "a[] = malloc")

    tri = tri.replace("void __VERIFIER_assert", "//void __VERIFIER_assertWASHERE")
    tri = tri.replace('__VERIFIER_assert(', 'assert(')
    tri = tri.replace("assume_abort_if_not(N", "assume(N")

    tri10 = tri.replace("100000", "10")
    tri10 = tri10.replace("N <= 2147483647/sizeof(int)", "N == 10")
    tri100 = tri10.replace("10", "100")
    triUB = tri10.replace("N == 10", "N > 0")
    triUB = triUB.replace("SIZE == 10", "SIZE > 0")

    dir = "tricera"

    write_three_files(tri10, tri100, triUB, fname, dir)

def replace_min_max_sum(s):
    for m in re.finditer(r"assert\(\\max\((?P<arr>\w+), 0, (?P<hi>\w+)\) (?P<cmp>[^\)]+)\);", s):
        s = s.replace(m.group(0), "\n"+get_max_loop(m.group('arr'), m.group('hi'), m.group('cmp'))+"\n// "+m.group(0))
    for m in re.finditer(r"assert\(\\min\((?P<arr>\w+), 0, (?P<hi>\w+)\) (?P<cmp>[^\)]+)\);", s):
        s = s.replace(m.group(0), "\n"+get_min_loop(m.group('arr'), m.group('hi'), m.group('cmp'))+"\n// "+m.group(0))
    for m in re.finditer(r"assert\(\\sum\((?P<arr>\w+), 0, (?P<hi>\w+)\) (?P<cmp>[^\)]+)\);", s):
        s = s.replace(m.group(0), "\n"+get_sum_loop(m.group('arr'), m.group('hi'), m.group('cmp'))+"\n// "+m.group(0))
    return s

def ours_to_tricera(s, fname):
    forall_stmt = "//@ assert \\forall int j; ((0 <= j) && (j < N)) ==> (arr[j] == (j*j*j*j));"
    exist_stmt = "//@ assert \exists int j; ((0 <= j) && (j < N)) && (arr[j] < (3-N));"
    tri = s.replace(forall_stmt, forall_stmt.replace("@", "") + "\n" + forall_loop)
    tri = tri.replace(exist_stmt, exist_stmt.replace("@", "") + "\n" + exist_loop)
    tri = replace_min_max_sum(tri)
    #tri = tri.replace("assert(\max(arr, 0, N) <= N-1);", get_max_assumes("assume"))
    tri = tri.replace("assert(bpack.max_voltage == \max(bpack.batt_voltages, 0, 10));",
                        get_max_loop("bpack.batt_voltages", "10", " == bpack.max_voltage"))

    tri10 = tri
    tri100 = tri10.replace("10", "100")
    s = """
  int N = __VERIFIER_nondet_int();
  assume(N > 0);
  """
    triUB = tri10.replace("int N = 10;", s)

    dir = "tricera"
    write_three_files(tri10, tri100, triUB, fname, dir)

def main():
    for fname in os.listdir("crafted_tests"):
        with open("crafted_tests/"+fname) as f:
            s = f.read()
            ours_to_seahorn(s, fname)
            ours_to_cpa(s, fname)
            ours_to_monocera(s, fname)
            ours_to_tricera(s, fname)
main()
