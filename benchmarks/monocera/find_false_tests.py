import os
import glob
import shutil

folders = ["forall","forall_new","exists","max","min","sum"]

for folder in folders:
    for fname in os.listdir("svcomp_tests/"+folder):
        for f in glob.glob('original_svcomp_folders/*/{}'.format(fname).replace(".c", "f.c")):
            if not os.path.exists("svcomp_tests/false_tests/"+folder):
                os.makedirs("svcomp_tests/false_tests/"+folder)
            shutil.copy2(f, "svcomp_tests/false_tests/"+folder)
