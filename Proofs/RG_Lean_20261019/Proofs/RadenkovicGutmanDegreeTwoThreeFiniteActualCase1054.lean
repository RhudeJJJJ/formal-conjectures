/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1054 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap1054 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap1054 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap1054_checked : acceptsGraphIso
    (source (graph core1054) (root 6) 0 2) DegreeOneSmallSpectrum345.graph sourceMap1054=true := by decide +kernel
theorem fusedMap1054_checked : acceptsGraphIso
    (fused (graph core1054) (root 6) 0 2) DegreeOneSmallSpectrum218.graph fusedMap1054=true := by decide +kernel
theorem certified1054 : Certified (graph core1054) (root 6) 0 2 :=
  of_native_maps core1054 DegreeOneSmallSpectrum345.graph DegreeOneSmallSpectrum218.graph
    sourceMap1054 fusedMap1054 sourceMap1054_checked fusedMap1054_checked
    DegreeTwoThreeFiniteComparisons.comparison1054
#print axioms sourceMap1054_checked
#print axioms fusedMap1054_checked
#print axioms certified1054
def sourceMap1054swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap1054swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap1054swap_checked : acceptsGraphIso
    (source (graph core1054) (root 6) 2 0) DegreeOneSmallSpectrum345.graph sourceMap1054swap=true := by decide +kernel
theorem fusedMap1054swap_checked : acceptsGraphIso
    (fused (graph core1054) (root 6) 2 0) DegreeOneSmallSpectrum218.graph fusedMap1054swap=true := by decide +kernel
theorem certified1054swap : Certified (graph core1054) (root 6) 2 0 :=
  of_native_maps core1054 DegreeOneSmallSpectrum345.graph DegreeOneSmallSpectrum218.graph
    sourceMap1054swap fusedMap1054swap sourceMap1054swap_checked fusedMap1054swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1054
#print axioms sourceMap1054swap_checked
#print axioms fusedMap1054swap_checked
#print axioms certified1054swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
