/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1125 : Family 8 := level8.get ⟨106,by decide⟩
def sourceMap1125 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap1125 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (fusedLabel 8 0 2 v)
theorem sourceMap1125_checked : acceptsGraphIso
    (source (graph core1125) (root 8) 0 2) DegreeOneSmallSpectrum1076.graph sourceMap1125=true := by decide +kernel
theorem fusedMap1125_checked : acceptsGraphIso
    (fused (graph core1125) (root 8) 0 2) DegreeOneSmallSpectrum1081.graph fusedMap1125=true := by decide +kernel
theorem certified1125 : Certified (graph core1125) (root 8) 0 2 :=
  of_native_maps core1125 DegreeOneSmallSpectrum1076.graph DegreeOneSmallSpectrum1081.graph
    sourceMap1125 fusedMap1125 sourceMap1125_checked fusedMap1125_checked
    DegreeTwoThreeFiniteComparisons.comparison1125
#print axioms sourceMap1125_checked
#print axioms fusedMap1125_checked
#print axioms certified1125
def sourceMap1125swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9,12] (sourceLabel 8 2 0 v)
def fusedMap1125swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (fusedLabel 8 2 0 v)
theorem sourceMap1125swap_checked : acceptsGraphIso
    (source (graph core1125) (root 8) 2 0) DegreeOneSmallSpectrum1076.graph sourceMap1125swap=true := by decide +kernel
theorem fusedMap1125swap_checked : acceptsGraphIso
    (fused (graph core1125) (root 8) 2 0) DegreeOneSmallSpectrum1081.graph fusedMap1125swap=true := by decide +kernel
theorem certified1125swap : Certified (graph core1125) (root 8) 2 0 :=
  of_native_maps core1125 DegreeOneSmallSpectrum1076.graph DegreeOneSmallSpectrum1081.graph
    sourceMap1125swap fusedMap1125swap sourceMap1125swap_checked fusedMap1125swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1125
#print axioms sourceMap1125swap_checked
#print axioms fusedMap1125swap_checked
#print axioms certified1125swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
