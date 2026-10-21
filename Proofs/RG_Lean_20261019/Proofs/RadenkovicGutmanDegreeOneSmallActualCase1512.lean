/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1512 : Family 9 := level9.get ⟨240,by decide⟩
def sourceMap1512 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1512 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 0 1 v)
theorem sourceMap1512_checked : acceptsGraphIso
    (source (graph core1512) (root 9) 0 1) DegreeOneSmallSpectrum1401.graph sourceMap1512=true := by decide +kernel
theorem fusedMap1512_checked : acceptsGraphIso
    (fused (graph core1512) (root 9) 0 1) DegreeOneSmallSpectrum1453.graph fusedMap1512=true := by decide +kernel
theorem certified1512 : Certified (graph core1512) (root 9) 0 1 :=
  of_native_maps core1512 DegreeOneSmallSpectrum1401.graph DegreeOneSmallSpectrum1453.graph
    sourceMap1512 fusedMap1512 sourceMap1512_checked fusedMap1512_checked
    DegreeOneSmallComparisons.comparison1512
#print axioms sourceMap1512_checked
#print axioms fusedMap1512_checked
#print axioms certified1512
def sourceMap1512swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1512swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (fusedLabel 9 1 0 v)
theorem sourceMap1512swap_checked : acceptsGraphIso
    (source (graph core1512) (root 9) 1 0) DegreeOneSmallSpectrum1401.graph sourceMap1512swap=true := by decide +kernel
theorem fusedMap1512swap_checked : acceptsGraphIso
    (fused (graph core1512) (root 9) 1 0) DegreeOneSmallSpectrum1453.graph fusedMap1512swap=true := by decide +kernel
theorem certified1512swap : Certified (graph core1512) (root 9) 1 0 :=
  of_native_maps core1512 DegreeOneSmallSpectrum1401.graph DegreeOneSmallSpectrum1453.graph
    sourceMap1512swap fusedMap1512swap sourceMap1512swap_checked fusedMap1512swap_checked
    DegreeOneSmallComparisons.comparison1512
#print axioms sourceMap1512swap_checked
#print axioms fusedMap1512swap_checked
#print axioms certified1512swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
