import time
import matplotlib.pyplot as plt
import numpy as np
import subprocess

def measure_runtime(tests):
    runtimes = []
    
    for test in tests:
        start_time = time.time()
        result = subprocess.check_output(["cargo", "test", test, "--", "--exact"])
        end_time = time.time()

        if "1 passed" in str(result): 
            runtime = end_time - start_time
            runtimes.append(runtime)
        else:
            print("Test unexpectedly failed!")
            print(result)
            exit(1)
    
    return runtimes

def plot_runtime_cdf(runtimes, n):
    # Set tests that timeout to have very large runtimes
    runtimes += [10000000 for i in range(n - len(runtimes))]
    runtimes.sort()
    y = np.arange(1, n+1) / n

    plt.figure(figsize=(5, 2))
    plt.subplots_adjust(bottom=0.18)
    plt.step(runtimes, y, where="post")
    plt.xlabel('Verification times (seconds)', fontsize=9)
    plt.ylabel('CDF', fontsize=9)
    plt.title('CDF of Verification Times', fontsize=9)
    plt.tick_params(axis='both', which='major', labelsize=6)
    plt.grid()
    plt.xlim(0, 25)
    plt.ylim(0, 1)
    plt.savefig("cdf.pdf")
    print(runtimes)

if __name__ == "__main__":

    with open("named_tests.txt") as file:
        named_tests = [line.rstrip() for line in file]

    with open("slow_tests.txt") as file:
        timeout_tests = [line.rstrip() for line in file]
    
    runtimes = measure_runtime(named_tests)
    n = len(runtimes) + len(timeout_tests)
    plot_runtime_cdf(runtimes, n)