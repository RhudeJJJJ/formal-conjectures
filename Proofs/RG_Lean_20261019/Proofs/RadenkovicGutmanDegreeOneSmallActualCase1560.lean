/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1560 : Family 9 := level9.get ⟨290,by decide⟩
def sourceMap1560 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1560 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (fusedLabel 9 0 1 v)
theorem sourceMap1560_checked : acceptsGraphIso
    (source (graph core1560) (root 9) 0 1) DegreeOneSmallSpectrum1395.graph sourceMap1560=true := by decide +kernel
theorem fusedMap1560_checked : acceptsGraphIso
    (fused (graph core1560) (root 9) 0 1) DegreeOneSmallSpectrum1511.graph fusedMap1560=true := by decide +kernel
theorem certified1560 : Certified (graph core1560) (root 9) 0 1 :=
  of_native_maps core1560 DegreeOneSmallSpectrum1395.graph DegreeOneSmallSpectrum1511.graph
    sourceMap1560 fusedMap1560 sourceMap1560_checked fusedMap1560_checked
    DegreeOneSmallComparisons.comparison1560
#print axioms sourceMap1560_checked
#print axioms fusedMap1560_checked
#print axioms certified1560
def sourceMap1560swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1560swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (fusedLabel 9 1 0 v)
theorem sourceMap1560swap_checked : acceptsGraphIso
    (source (graph core1560) (root 9) 1 0) DegreeOneSmallSpectrum1395.graph sourceMap1560swap=true := by decide +kernel
theorem fusedMap1560swap_checked : acceptsGraphIso
    (fused (graph core1560) (root 9) 1 0) DegreeOneSmallSpectrum1511.graph fusedMap1560swap=true := by decide +kernel
theorem certified1560swap : Certified (graph core1560) (root 9) 1 0 :=
  of_native_maps core1560 DegreeOneSmallSpectrum1395.graph DegreeOneSmallSpectrum1511.graph
    sourceMap1560swap fusedMap1560swap sourceMap1560swap_checked fusedMap1560swap_checked
    DegreeOneSmallComparisons.comparison1560
#print axioms sourceMap1560swap_checked
#print axioms fusedMap1560swap_checked
#print axioms certified1560swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
