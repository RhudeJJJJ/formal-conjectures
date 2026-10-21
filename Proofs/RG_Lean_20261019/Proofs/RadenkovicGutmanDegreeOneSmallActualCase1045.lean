/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1045 : Family 8 := level8.get ⟨120,by decide⟩
def sourceMap1045 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1045 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1045_checked : acceptsGraphIso
    (source (graph core1045) (root 8) 0 2) DegreeOneSmallSpectrum1188.graph sourceMap1045=true := by decide +kernel
theorem fusedMap1045_checked : acceptsGraphIso
    (fused (graph core1045) (root 8) 0 2) DegreeOneSmallSpectrum1189.graph fusedMap1045=true := by decide +kernel
theorem certified1045 : Certified (graph core1045) (root 8) 0 2 :=
  of_native_maps core1045 DegreeOneSmallSpectrum1188.graph DegreeOneSmallSpectrum1189.graph
    sourceMap1045 fusedMap1045 sourceMap1045_checked fusedMap1045_checked
    DegreeOneSmallComparisons.comparison1045
#print axioms sourceMap1045_checked
#print axioms fusedMap1045_checked
#print axioms certified1045
def sourceMap1045swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1045swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1045swap_checked : acceptsGraphIso
    (source (graph core1045) (root 8) 2 0) DegreeOneSmallSpectrum1188.graph sourceMap1045swap=true := by decide +kernel
theorem fusedMap1045swap_checked : acceptsGraphIso
    (fused (graph core1045) (root 8) 2 0) DegreeOneSmallSpectrum1189.graph fusedMap1045swap=true := by decide +kernel
theorem certified1045swap : Certified (graph core1045) (root 8) 2 0 :=
  of_native_maps core1045 DegreeOneSmallSpectrum1188.graph DegreeOneSmallSpectrum1189.graph
    sourceMap1045swap fusedMap1045swap sourceMap1045swap_checked fusedMap1045swap_checked
    DegreeOneSmallComparisons.comparison1045
#print axioms sourceMap1045swap_checked
#print axioms fusedMap1045swap_checked
#print axioms certified1045swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
