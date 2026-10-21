/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1474 : Family 9 := level9.get ⟨208,by decide⟩
def sourceMap1474 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1474 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1474_checked : acceptsGraphIso
    (source (graph core1474) (root 9) 0 1) DegreeOneSmallSpectrum1336.graph sourceMap1474=true := by decide +kernel
theorem fusedMap1474_checked : acceptsGraphIso
    (fused (graph core1474) (root 9) 0 1) DegreeOneSmallSpectrum1347.graph fusedMap1474=true := by decide +kernel
theorem certified1474 : Certified (graph core1474) (root 9) 0 1 :=
  of_native_maps core1474 DegreeOneSmallSpectrum1336.graph DegreeOneSmallSpectrum1347.graph
    sourceMap1474 fusedMap1474 sourceMap1474_checked fusedMap1474_checked
    DegreeOneSmallComparisons.comparison1474
#print axioms sourceMap1474_checked
#print axioms fusedMap1474_checked
#print axioms certified1474
def sourceMap1474swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1474swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1474swap_checked : acceptsGraphIso
    (source (graph core1474) (root 9) 1 0) DegreeOneSmallSpectrum1336.graph sourceMap1474swap=true := by decide +kernel
theorem fusedMap1474swap_checked : acceptsGraphIso
    (fused (graph core1474) (root 9) 1 0) DegreeOneSmallSpectrum1347.graph fusedMap1474swap=true := by decide +kernel
theorem certified1474swap : Certified (graph core1474) (root 9) 1 0 :=
  of_native_maps core1474 DegreeOneSmallSpectrum1336.graph DegreeOneSmallSpectrum1347.graph
    sourceMap1474swap fusedMap1474swap sourceMap1474swap_checked fusedMap1474swap_checked
    DegreeOneSmallComparisons.comparison1474
#print axioms sourceMap1474swap_checked
#print axioms fusedMap1474swap_checked
#print axioms certified1474swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
