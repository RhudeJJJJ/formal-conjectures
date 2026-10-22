/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1079 : Family 7 := level7.get ⟨67,by decide⟩
def sourceMap1079 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9] (sourceLabel 7 0 2 v)
def fusedMap1079 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap1079_checked : acceptsGraphIso
    (source (graph core1079) (root 7) 0 2) DegreeOneSmallSpectrum657.graph sourceMap1079=true := by decide +kernel
theorem fusedMap1079_checked : acceptsGraphIso
    (fused (graph core1079) (root 7) 0 2) DegreeOneSmallSpectrum407.graph fusedMap1079=true := by decide +kernel
theorem certified1079 : Certified (graph core1079) (root 7) 0 2 :=
  of_native_maps core1079 DegreeOneSmallSpectrum657.graph DegreeOneSmallSpectrum407.graph
    sourceMap1079 fusedMap1079 sourceMap1079_checked fusedMap1079_checked
    DegreeTwoThreeFiniteComparisons.comparison1079
#print axioms sourceMap1079_checked
#print axioms fusedMap1079_checked
#print axioms certified1079
def sourceMap1079swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11] (sourceLabel 7 2 0 v)
def fusedMap1079swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap1079swap_checked : acceptsGraphIso
    (source (graph core1079) (root 7) 2 0) DegreeOneSmallSpectrum657.graph sourceMap1079swap=true := by decide +kernel
theorem fusedMap1079swap_checked : acceptsGraphIso
    (fused (graph core1079) (root 7) 2 0) DegreeOneSmallSpectrum407.graph fusedMap1079swap=true := by decide +kernel
theorem certified1079swap : Certified (graph core1079) (root 7) 2 0 :=
  of_native_maps core1079 DegreeOneSmallSpectrum657.graph DegreeOneSmallSpectrum407.graph
    sourceMap1079swap fusedMap1079swap sourceMap1079swap_checked fusedMap1079swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1079
#print axioms sourceMap1079swap_checked
#print axioms fusedMap1079swap_checked
#print axioms certified1079swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
