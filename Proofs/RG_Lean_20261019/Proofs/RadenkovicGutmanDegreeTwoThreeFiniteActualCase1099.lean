/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1099 : Family 8 := level8.get ⟨24,by decide⟩
def sourceMap1099 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap1099 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1099_checked : acceptsGraphIso
    (source (graph core1099) (root 8) 0 2) DegreeOneSmallSpectrum954.graph sourceMap1099=true := by decide +kernel
theorem fusedMap1099_checked : acceptsGraphIso
    (fused (graph core1099) (root 8) 0 2) DegreeOneSmallSpectrum965.graph fusedMap1099=true := by decide +kernel
theorem certified1099 : Certified (graph core1099) (root 8) 0 2 :=
  of_native_maps core1099 DegreeOneSmallSpectrum954.graph DegreeOneSmallSpectrum965.graph
    sourceMap1099 fusedMap1099 sourceMap1099_checked fusedMap1099_checked
    DegreeTwoThreeFiniteComparisons.comparison1099
#print axioms sourceMap1099_checked
#print axioms fusedMap1099_checked
#print axioms certified1099
def sourceMap1099swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,2,3,4,6] (sourceLabel 8 2 0 v)
def fusedMap1099swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1099swap_checked : acceptsGraphIso
    (source (graph core1099) (root 8) 2 0) DegreeOneSmallSpectrum954.graph sourceMap1099swap=true := by decide +kernel
theorem fusedMap1099swap_checked : acceptsGraphIso
    (fused (graph core1099) (root 8) 2 0) DegreeOneSmallSpectrum965.graph fusedMap1099swap=true := by decide +kernel
theorem certified1099swap : Certified (graph core1099) (root 8) 2 0 :=
  of_native_maps core1099 DegreeOneSmallSpectrum954.graph DegreeOneSmallSpectrum965.graph
    sourceMap1099swap fusedMap1099swap sourceMap1099swap_checked fusedMap1099swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1099
#print axioms sourceMap1099swap_checked
#print axioms fusedMap1099swap_checked
#print axioms certified1099swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
