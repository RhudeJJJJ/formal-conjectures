/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1502 : Family 9 := level9.get ⟨231,by decide⟩
def sourceMap1502 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1502 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1502_checked : acceptsGraphIso
    (source (graph core1502) (root 9) 0 1) DegreeOneSmallSpectrum1416.graph sourceMap1502=true := by decide +kernel
theorem fusedMap1502_checked : acceptsGraphIso
    (fused (graph core1502) (root 9) 0 1) DegreeOneSmallSpectrum1418.graph fusedMap1502=true := by decide +kernel
theorem certified1502 : Certified (graph core1502) (root 9) 0 1 :=
  of_native_maps core1502 DegreeOneSmallSpectrum1416.graph DegreeOneSmallSpectrum1418.graph
    sourceMap1502 fusedMap1502 sourceMap1502_checked fusedMap1502_checked
    DegreeOneSmallComparisons.comparison1502
#print axioms sourceMap1502_checked
#print axioms fusedMap1502_checked
#print axioms certified1502
def sourceMap1502swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1502swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1502swap_checked : acceptsGraphIso
    (source (graph core1502) (root 9) 1 0) DegreeOneSmallSpectrum1416.graph sourceMap1502swap=true := by decide +kernel
theorem fusedMap1502swap_checked : acceptsGraphIso
    (fused (graph core1502) (root 9) 1 0) DegreeOneSmallSpectrum1418.graph fusedMap1502swap=true := by decide +kernel
theorem certified1502swap : Certified (graph core1502) (root 9) 1 0 :=
  of_native_maps core1502 DegreeOneSmallSpectrum1416.graph DegreeOneSmallSpectrum1418.graph
    sourceMap1502swap fusedMap1502swap sourceMap1502swap_checked fusedMap1502swap_checked
    DegreeOneSmallComparisons.comparison1502
#print axioms sourceMap1502swap_checked
#print axioms fusedMap1502swap_checked
#print axioms certified1502swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
