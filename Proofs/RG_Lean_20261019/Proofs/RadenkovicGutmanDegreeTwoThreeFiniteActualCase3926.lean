/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3926 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap3926 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,8,6,7,1,0,9,10,11,12] (sourceLabel 4 1 5 v)
def fusedMap3926 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 1 5 v)
theorem sourceMap3926_checked : acceptsGraphIso
    (source (graph core3926) (root 4) 1 5) DegreeOneSmallSpectrum1095.graph sourceMap3926=true := by decide +kernel
theorem fusedMap3926_checked : acceptsGraphIso
    (fused (graph core3926) (root 4) 1 5) DegreeOneSmallSpectrum879.graph fusedMap3926=true := by decide +kernel
theorem certified3926 : Certified (graph core3926) (root 4) 1 5 :=
  of_native_maps core3926 DegreeOneSmallSpectrum1095.graph DegreeOneSmallSpectrum879.graph
    sourceMap3926 fusedMap3926 sourceMap3926_checked fusedMap3926_checked
    DegreeTwoThreeFiniteComparisons.comparison3926
#print axioms sourceMap3926_checked
#print axioms fusedMap3926_checked
#print axioms certified3926
def sourceMap3926swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,3,4,5,8,1,0,9,10,11,12,6,7] (sourceLabel 4 5 1 v)
def fusedMap3926swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 5 1 v)
theorem sourceMap3926swap_checked : acceptsGraphIso
    (source (graph core3926) (root 4) 5 1) DegreeOneSmallSpectrum1095.graph sourceMap3926swap=true := by decide +kernel
theorem fusedMap3926swap_checked : acceptsGraphIso
    (fused (graph core3926) (root 4) 5 1) DegreeOneSmallSpectrum879.graph fusedMap3926swap=true := by decide +kernel
theorem certified3926swap : Certified (graph core3926) (root 4) 5 1 :=
  of_native_maps core3926 DegreeOneSmallSpectrum1095.graph DegreeOneSmallSpectrum879.graph
    sourceMap3926swap fusedMap3926swap sourceMap3926swap_checked fusedMap3926swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3926
#print axioms sourceMap3926swap_checked
#print axioms fusedMap3926swap_checked
#print axioms certified3926swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
