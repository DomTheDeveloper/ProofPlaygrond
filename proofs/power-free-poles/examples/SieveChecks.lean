module

import all PowerFreeSieve

open PowerFree.Sieve

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem squarefree_first_hundred : powerFreeCount 2 100 = 61 := by decide
theorem cubefree_first_hundred : powerFreeCount 3 100 = 85 := by decide
theorem squarefree_first_thousand : powerFreeCount 2 1000 = 608 := by decide
theorem cubefree_first_thousand : powerFreeCount 3 1000 = 833 := by decide

#print axioms PowerFree.Sieve.countAvoiding_eq
#print axioms PowerFree.Sieve.avoids_iff
#print axioms PowerFree.Sieve.powerFreeCount_eq
#print axioms squarefree_first_thousand
#print axioms cubefree_first_thousand
