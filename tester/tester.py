import sys
import os
import subprocess

exec_path = sys.argv[1]
testsuite_path = sys.argv[2] if len(sys.argv) > 2 else os.getcwd()
bad_path = os.path.join(testsuite_path, "bad")

def run_exec(path, input=None):
    return subprocess.run([exec_path, path], input=input, stdout=subprocess.PIPE, universal_newlines=True)

def handle_good_suite():
    good_path = os.path.join(testsuite_path, "good")
    names = set(os.path.splitext(f)[0] for f in os.listdir(good_path) if os.path.isfile(os.path.join(good_path, f)))
    names = sorted(list(names))

    def run_good_test(name):
        code_path = os.path.join(good_path, name + ".jl")
        output_path = os.path.join(good_path, name + ".output")
        input_path = os.path.join(good_path, name + ".input")

        with open(output_path) as f:
            expected_output = f.read()

        try:
            with open(input_path) as f:
                given_input = f.read()
        except:
            given_input = None

        res = run_exec(code_path, given_input)
        print("Test {} : {}".format(name, "OK" if expected_output == res.stdout else "FAIL"))


    for name in names:
        run_good_test(name)

handle_good_suite()
