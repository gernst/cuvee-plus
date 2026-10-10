import os
import re
import shutil
import glob
import sys

DEBUG = False

NO_MALLOC = False

#Toggle FALSE_TESTS depending on want to convert safe unsafe tests
FALSE_TESTS = False

SVCOMP_PATH = "svcomp_tests"
OUT_PATH = "polished_tests"
if FALSE_TESTS:
    SVCOMP_PATH = SVCOMP_PATH + "/false_tests"
    OUT_PATH = OUT_PATH + "/false_tests"



MAX_PATH = SVCOMP_PATH + "/max"
MIN_PATH = SVCOMP_PATH + "/min"
SUM_PATH = SVCOMP_PATH + "/sum"
FORALL_PATH = SVCOMP_PATH + "/forall"
#FORALL_NEW_PATH = SVCOMP_PATH + "/forall_new"
TOOLS = ["monocera", "seahorn", "tricera", "cpa"]

max_files = os.listdir(MAX_PATH)
min_files = os.listdir(MIN_PATH)
forall_files = os.listdir(FORALL_PATH)
sum_files = os.listdir(SUM_PATH)
#forall_new_files = os.listdir(FORALL_NEW_PATH)

sum_files = os.listdir(SUM_PATH)

file_lists = {MIN_PATH:min_files, MAX_PATH:max_files,
                SUM_PATH:sum_files,FORALL_PATH:forall_files} #,FORALL_NEW_PATH:forall_new_files}
forall_loop1 = """
  i=0;
  while(i < N) {
   __VERIFIER_assert(a[i]==i);
   i=i+1;
  }
"""

forall_loop2 = """
  while( i < 10000 )
  {
	__VERIFIER_assert( a[j] == b[j] );
        i = i+1;
        j = j+1;
  }
"""

max_loop1 = """
      for(int k=4;k<i;k++)
        __VERIFIER_assert(a[k] <= 0);
"""

sum_loop1 ="""
	for(i=0; i<N; i++)
	{
		if(i==0) {
			sum[0] = 0;
		} else {
			sum[0] = sum[0] + a[i];
		}
	}
"""

sum_loop2 = """
	for(i=0; i<N; i++)
	{
		sum[0] = sum[0] + a[i];
	}
"""

sum_loop3 = """
	for(i=0;i<N;i++)
	{
		sum[0] = sum[0] + a[i];
	}
"""

sum_loops = [sum_loop1, sum_loop2, sum_loop3]
max_loops = [max_loop1]
forall_loops = [forall_loop1, forall_loop2]



def write_to_file(s, path):
    with open(path, 'w') as f:
        f.write(s)





def get_max_loop(a, N, cmp):
    s =   """
  int max = {0}[0];
  for (int i = 0; i < {1}; i++) {{
      if ({0}[i] > max) {{
          max = {0}[i];
      }}
  }}
  assert(max{2});""".format(a,N, cmp)
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

asm_s = """
void __VERIFIER_assume(int cond) {
    if (!cond) {
        while (1) {};
    }
}

"""
def sv_to_cpa(s, dir, fname):
    if NO_MALLOC:
        s = mallocs_to_arrs(s)
    return asm_s + s

def mallocs_to_arrs(s):
    for m in re.finditer(r"(\w.*)\s+\*(\w+) = malloc\((.*)\);", s):
        size = re.sub(r"sizeof\s*\([^\)]+\)", "1", m.group(3))
        size = size.replace("1*", "")
        s = s.replace(m.group(0), "//"+m.group(0) +"\n\t"+m.group(1)+ " " +m.group(2)+ "["+size+"];")
    return s

def comment_out(s, sub):
    return re.sub(r".*"+re.escape(sub), "// "+sub,s)
    for m in re.finditer(sub, s):
        tmp = m.group()
        s2 = s2.replace(tmp, "/* "+tmp+"*/")
    return s2

def assert_sum(a, lo, hi, rel, val):
    return "assert(\\sum({}, {}, {}) {} {});".format(a, lo, hi, rel, val)

def assert_max(a, lo, hi, rel, val):
    return "assert(\\max({}, {}, {}) {} {});".format(a, lo, hi, rel, val)

def assert_min(a, lo, hi, rel, val, hi_rel):
    if hi_rel == "<=": hi = hi + " + 1"
    return "assert(\\min({}, {}, {}) {} {});".format(a, lo, hi, rel, val)

def assert_forall(a, lo, hi, i, P, jjj):
    for m in re.finditer(r"[^\w]({})[^\w]".format(i), P):
        P = P.replace(m.group(1), jjj)
        P = P.replace("majjj", "max")
    return "//@ assert \\forall int {jjj}; (({lo} <= {jjj}) && ({jjj} {hi})) ==> ({P});".format(jjj=jjj, lo=lo, hi=hi, P=P)

def sv_to_monocera(s, dir, fname):
    for m in re.finditer("#define (\w+) (\w+)", s):
        s = s.replace(m.group(0), "// "+m.group(0))
        s = s.replace(m.group(1), m.group(2))
    if NO_MALLOC:
        s = mallocs_to_arrs(s)
    else:
        s = s.replace("*a = malloc", "a[] = malloc")
        s = s.replace("*b = malloc", "b[] = malloc")
        s = s.replace("*c = malloc", "c[] = malloc")
        s = s.replace("*x = malloc", "x[] = malloc")

    s = comment_out(s, r"extern void")
    if dir == MAX_PATH:
        max_regex = r"for\s*\(\s*(int\s*)?\w+\s*=\s*([0-9])\s*;\s*\w+\s*<\s*(\w+)\s*;\s*.+\s*\)\s*\{?\s*__VERIFIER_assert\(\s*(\w+)\[.*\]\s*(<=)\s*(.+)\s*\)\s*\s*;\s*\}?"
        for m in re.finditer(max_regex, s):
            s=s.replace(m.group(0), "\n/*"+m.group(0)+"*/"+"\n\t"+assert_max(m.group(4), m.group(2), m.group(3), m.group(5), m.group(6))+"\n")
    if dir == MIN_PATH:
        min_regex = r"for\s*\(\s*(int\s*)?\w+\s*=\s*([0-9])\s*;\s*\w+\s*(<=?)\s*([^;]+)\s*;\s*.+\s*\)\s*\{?\s*__VERIFIER_assert\(\s*(\w+)\[.*\]\s*(>=?)\s*(.+)\s*\)\s*\s*;\s*\}?"
        for m in re.finditer(min_regex, s):
            s=s.replace(m.group(0), "\n/*"+m.group(0)+"*/"+"\n\t"+assert_min(m.group(5), m.group(2), m.group(4), m.group(6), m.group(7), m.group(3))+"\n")
    if dir == SUM_PATH:
        for loop in sum_loops:
            s = s.replace(loop, "\n/*"+loop+"*/\n")
        for m in re.finditer(r"__VERIFIER_assert\(sum\[0\] (<=|==|>=|!=) ([^\)]*)\);", s):
            s = s.replace(m.group(), "//"+m.group()+"\n"+assert_sum("a", "0", "N", m.group(1), m.group(2)))
    if dir == FORALL_PATH:# or dir == FORALL_NEW_PATH:
        found = False
        s = s.replace(forall_loop1, "\n/*"+forall_loop1+"*/\n\t"+assert_forall("a", "0", "< N", "i", "a[i]==i", "jjj")+"\n")
        s = s.replace(forall_loop2, "\n/*"+forall_loop2+"*/\n\t"+assert_forall("a", "0", "< N", "j", "a[j] == b[j]", "jjj")+"\n")
    #    forall_regex = r"\s*for\s*\(\s*(int\s*)?\w+\s*=\s*([0-9])\s*;\s*\w+\s*(<=?\s*[^;]+)\s*;\s*.+\s*\)\s*\{?\s*__VERIFIER_assert\(\(?\s*(\w+)\[\s*(\w+)\s*\]\s*((?:\s*%\s*\w+\s*)?(?:<[^=]|>[^=]|>=|<=|==|!=))\s*(.+)\s*\)\s*;\s*\}?"

        forall_regex = r"\s*for\s*\(\s*(?:int\s*)?\w+\s*=\s*(?P<lo>[0-9])\s*;\s*\w+\s*(?P<hi><=?\s*[^;]+)\s*;\s*.+\s*\)\s*\{?\s*__VERIFIER_assert\((?P<P>[^\w]*(?P<a>\w+)\[\s*(?P<i>\w+)\s*\].*\s*)\)\s*;\s*\}?"

        for m in re.finditer(forall_regex, s):
            found = True
            s=s.replace(m.group(0), "\n/*"+m.group(0)+"*/"+"\n\t"+assert_forall(m.group("a"), m.group("lo"), m.group("hi"), m.group("i"), m.group("P"), "jjj")+"\n")
        if not found and DEBUG: print("could not find any forall-quant for: {}".format(fname))
    return s

def sv_to_seahorn(s, dir, fname):

    if NO_MALLOC:
        s = mallocs_to_arrs(s)

    s = s.replace("void __VERIFIER_assert", "//void __VERIFIER_assertWASHERE")
    s = s.replace('__VERIFIER_assert(', 'sassert(')
    s = s.replace("assume_abort_if_not(N", "assume(N")
    s =  "#include<seahorn/seahorn.h>\n\n" + s
    return s


def sv_to_tricera(s, dir, fname):
    for m in re.finditer("#define (\w+) (\w+)", s):
        s = s.replace(m.group(0), "// "+m.group(0))
        s = s.replace(m.group(1), m.group(2))
    if NO_MALLOC:
        s = mallocs_to_arrs(s)
    else:
        s = s.replace("*a = malloc", "a[] = malloc")
        s = s.replace("*b = malloc", "b[] = malloc")
        s = s.replace("*c = malloc", "c[] = malloc")
        s = s.replace("*x = malloc", "x[] = malloc")

    s = comment_out(s, r"extern void")

    s = s.replace("void __VERIFIER_assert", "//void __VERIFIER_assertWASHERE")
    s = s.replace('__VERIFIER_assert(', 'assert(')

    return s

def fix_and_write(s, tool, dir, fname):
    tool_to_func = {"monocera":sv_to_monocera, "seahorn":sv_to_seahorn,
                    "tricera":sv_to_tricera, "cpa":sv_to_cpa}
    outpath = OUT_PATH
    if NO_MALLOC:
        outpath += "_nomalloc"
    folder  = "{}/{}/{}".format(outpath, tool, dir.replace("svcomp_tests/", "").replace("false_tests/",""))
    if not os.path.exists(folder):
        os.makedirs(folder)
    s = tool_to_func[tool](s, dir, fname)

    #add yml file
    for f in glob.glob('yml_files/{}'.format(fname).replace(".c", ".yml")):
        shutil.copy2(f, folder)

    write_to_file(s, "{}/{}".format(folder, fname))

def main():
    global NO_MALLOC
    if len(sys.argv) > 1 and sys.argv[1] == "-nomalloc":
        NO_MALLOC = True
    else:
        NO_MALLOC = False

    for (dir, fnames) in file_lists.items():
        for fname in fnames:
            with open(dir+"/"+fname) as f:
                s = f.read()
            [fix_and_write(s, tool, dir, fname) for tool in TOOLS]
main()
