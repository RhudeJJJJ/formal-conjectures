/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1704 : Family 9 := level9.get ⟨469,by decide⟩
def sourceMap1704 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1704 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1704_checked : acceptsGraphIso
    (source (graph core1704) (root 9) 0 1) DegreeOneSmallSpectrum1962.graph sourceMap1704=true := by decide +kernel
theorem fusedMap1704_checked : acceptsGraphIso
    (fused (graph core1704) (root 9) 0 1) DegreeOneSmallSpectrum1415.graph fusedMap1704=true := by decide +kernel
theorem certified1704 : Certified (graph core1704) (root 9) 0 1 :=
  of_native_maps core1704 DegreeOneSmallSpectrum1962.graph DegreeOneSmallSpectrum1415.graph
    sourceMap1704 fusedMap1704 sourceMap1704_checked fusedMap1704_checked
    DegreeOneSmallComparisons.comparison1704
#print axioms sourceMap1704_checked
#print axioms fusedMap1704_checked
#print axioms certified1704
def sourceMap1704swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1704swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1704swap_checked : acceptsGraphIso
    (source (graph core1704) (root 9) 1 0) DegreeOneSmallSpectrum1962.graph sourceMap1704swap=true := by decide +kernel
theorem fusedMap1704swap_checked : acceptsGraphIso
    (fused (graph core1704) (root 9) 1 0) DegreeOneSmallSpectrum1415.graph fusedMap1704swap=true := by decide +kernel
theorem certified1704swap : Certified (graph core1704) (root 9) 1 0 :=
  of_native_maps core1704 DegreeOneSmallSpectrum1962.graph DegreeOneSmallSpectrum1415.graph
    sourceMap1704swap fusedMap1704swap sourceMap1704swap_checked fusedMap1704swap_checked
    DegreeOneSmallComparisons.comparison1704
#print axioms sourceMap1704swap_checked
#print axioms fusedMap1704swap_checked
#print axioms certified1704swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
