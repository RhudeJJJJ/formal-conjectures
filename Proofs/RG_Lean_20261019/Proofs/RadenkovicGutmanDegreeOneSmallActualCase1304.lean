/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1304 : Family 9 := level9.get ⟨70,by decide⟩
def sourceMap1304 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1304 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1304_checked : acceptsGraphIso
    (source (graph core1304) (root 9) 0 1) DegreeOneSmallSpectrum1327.graph sourceMap1304=true := by decide +kernel
theorem fusedMap1304_checked : acceptsGraphIso
    (fused (graph core1304) (root 9) 0 1) DegreeOneSmallSpectrum910.graph fusedMap1304=true := by decide +kernel
theorem certified1304 : Certified (graph core1304) (root 9) 0 1 :=
  of_native_maps core1304 DegreeOneSmallSpectrum1327.graph DegreeOneSmallSpectrum910.graph
    sourceMap1304 fusedMap1304 sourceMap1304_checked fusedMap1304_checked
    DegreeOneSmallComparisons.comparison1304
#print axioms sourceMap1304_checked
#print axioms fusedMap1304_checked
#print axioms certified1304
def sourceMap1304swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1304swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1304swap_checked : acceptsGraphIso
    (source (graph core1304) (root 9) 1 0) DegreeOneSmallSpectrum1327.graph sourceMap1304swap=true := by decide +kernel
theorem fusedMap1304swap_checked : acceptsGraphIso
    (fused (graph core1304) (root 9) 1 0) DegreeOneSmallSpectrum910.graph fusedMap1304swap=true := by decide +kernel
theorem certified1304swap : Certified (graph core1304) (root 9) 1 0 :=
  of_native_maps core1304 DegreeOneSmallSpectrum1327.graph DegreeOneSmallSpectrum910.graph
    sourceMap1304swap fusedMap1304swap sourceMap1304swap_checked fusedMap1304swap_checked
    DegreeOneSmallComparisons.comparison1304
#print axioms sourceMap1304swap_checked
#print axioms fusedMap1304swap_checked
#print axioms certified1304swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
