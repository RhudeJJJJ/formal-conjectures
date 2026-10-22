/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1119 : Family 8 := level8.get ⟨89,by decide⟩
def sourceMap1119 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap1119 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,5,6,1,2,3,4] (fusedLabel 8 0 2 v)
theorem sourceMap1119_checked : acceptsGraphIso
    (source (graph core1119) (root 8) 0 2) DegreeOneSmallSpectrum1485.graph sourceMap1119=true := by decide +kernel
theorem fusedMap1119_checked : acceptsGraphIso
    (fused (graph core1119) (root 8) 0 2) DegreeOneSmallSpectrum970.graph fusedMap1119=true := by decide +kernel
theorem certified1119 : Certified (graph core1119) (root 8) 0 2 :=
  of_native_maps core1119 DegreeOneSmallSpectrum1485.graph DegreeOneSmallSpectrum970.graph
    sourceMap1119 fusedMap1119 sourceMap1119_checked fusedMap1119_checked
    DegreeTwoThreeFiniteComparisons.comparison1119
#print axioms sourceMap1119_checked
#print axioms fusedMap1119_checked
#print axioms certified1119
def sourceMap1119swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,2,3,4,7] (sourceLabel 8 2 0 v)
def fusedMap1119swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,5,6,1,2,3,4] (fusedLabel 8 2 0 v)
theorem sourceMap1119swap_checked : acceptsGraphIso
    (source (graph core1119) (root 8) 2 0) DegreeOneSmallSpectrum1485.graph sourceMap1119swap=true := by decide +kernel
theorem fusedMap1119swap_checked : acceptsGraphIso
    (fused (graph core1119) (root 8) 2 0) DegreeOneSmallSpectrum970.graph fusedMap1119swap=true := by decide +kernel
theorem certified1119swap : Certified (graph core1119) (root 8) 2 0 :=
  of_native_maps core1119 DegreeOneSmallSpectrum1485.graph DegreeOneSmallSpectrum970.graph
    sourceMap1119swap fusedMap1119swap sourceMap1119swap_checked fusedMap1119swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1119
#print axioms sourceMap1119swap_checked
#print axioms fusedMap1119swap_checked
#print axioms certified1119swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
