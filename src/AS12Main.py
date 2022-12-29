import sgxp23
import time

clauseSet = sgxp23.parseDIMACS("data/problem.cnf")
startTime = time.time()

print(sgxp23.dpll_sat_solve(clauseSet, []))

endTime = time.time()
print(endTime - startTime)