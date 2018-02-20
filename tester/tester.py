import sys
import os
import subprocess

exec_path = sys.argv[1]
testsuite_path = sys.argv[2]
exec_opt = sys.argv[3:] if len(sys.argv) > 3 else []
total_ok = 0
total_fail = 0

def run_exec(path, input=None):
    return subprocess.run([exec_path, path] + exec_opt, input=input, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)

def result_test(name, success, added_infos=None):
    global total_ok, total_fail
    if success:
        total_ok += 1
    else:
        total_fail += 1

    print("Test {}\t\t: {} {}".format(name, "OK" if success else "FAIL", added_infos if added_infos else ""))

def handle_suite(path, run_test):
    names = set(os.path.splitext(f)[0] for f in os.listdir(path) if os.path.isfile(os.path.join(path, f)))
    names = sorted(list(names))

    for name in names:
        run_test(name)

def handle_good_suite(next_path):
    good_path = os.path.join(testsuite_path, next_path)

    def run_good_test(name):
        code_path = os.path.join(good_path, name + ".yal")
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
        result_test(name, expected_output == res.stdout)

    handle_suite(good_path, run_good_test)

def handle_bad_suite():
    bad_path = os.path.join(testsuite_path, "bad")

    def run_bad_test(name):
        code_path = os.path.join(bad_path, name + ".yal")

        res = run_exec(code_path)
        result_test(name, res.returncode == 1, "(exit code {})".format(res.returncode))
    handle_suite(bad_path, run_bad_test)

handle_good_suite("good")
handle_good_suite("extensions/arrays1")
handle_good_suite("extensions/arrays2")
handle_good_suite("perso")
handle_bad_suite()

print("----------------------------------")
print("{} tests | {} fails ({}%)".format(total_ok + total_fail, total_fail, 100 * total_fail / (total_ok + total_fail)))
