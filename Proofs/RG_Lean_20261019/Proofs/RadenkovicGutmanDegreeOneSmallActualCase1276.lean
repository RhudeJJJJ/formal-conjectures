/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1276 : Family 9 := level9.get ⟨50,by decide⟩
def sourceMap1276 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1276 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1276_checked : acceptsGraphIso
    (source (graph core1276) (root 9) 0 1) DegreeOneSmallSpectrum1131.graph sourceMap1276=true := by decide +kernel
theorem fusedMap1276_checked : acceptsGraphIso
    (fused (graph core1276) (root 9) 0 1) DegreeOneSmallSpectrum872.graph fusedMap1276=true := by decide +kernel
theorem certified1276 : Certified (graph core1276) (root 9) 0 1 :=
  of_native_maps core1276 DegreeOneSmallSpectrum1131.graph DegreeOneSmallSpectrum872.graph
    sourceMap1276 fusedMap1276 sourceMap1276_checked fusedMap1276_checked
    DegreeOneSmallComparisons.comparison1276
#print axioms sourceMap1276_checked
#print axioms fusedMap1276_checked
#print axioms certified1276
def sourceMap1276swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1276swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1276swap_checked : acceptsGraphIso
    (source (graph core1276) (root 9) 1 0) DegreeOneSmallSpectrum1131.graph sourceMap1276swap=true := by decide +kernel
theorem fusedMap1276swap_checked : acceptsGraphIso
    (fused (graph core1276) (root 9) 1 0) DegreeOneSmallSpectrum872.graph fusedMap1276swap=true := by decide +kernel
theorem certified1276swap : Certified (graph core1276) (root 9) 1 0 :=
  of_native_maps core1276 DegreeOneSmallSpectrum1131.graph DegreeOneSmallSpectrum872.graph
    sourceMap1276swap fusedMap1276swap sourceMap1276swap_checked fusedMap1276swap_checked
    DegreeOneSmallComparisons.comparison1276
#print axioms sourceMap1276swap_checked
#print axioms fusedMap1276swap_checked
#print axioms certified1276swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
