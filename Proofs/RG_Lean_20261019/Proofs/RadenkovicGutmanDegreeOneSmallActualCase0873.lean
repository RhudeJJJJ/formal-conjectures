/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0873 : Family 8 := level8.get ⟨44,by decide⟩
def sourceMap0873 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0873 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0873_checked : acceptsGraphIso
    (source (graph core0873) (root 8) 0 2) DegreeOneSmallSpectrum1210.graph sourceMap0873=true := by decide +kernel
theorem fusedMap0873_checked : acceptsGraphIso
    (fused (graph core0873) (root 8) 0 2) DegreeOneSmallSpectrum880.graph fusedMap0873=true := by decide +kernel
theorem certified0873 : Certified (graph core0873) (root 8) 0 2 :=
  of_native_maps core0873 DegreeOneSmallSpectrum1210.graph DegreeOneSmallSpectrum880.graph
    sourceMap0873 fusedMap0873 sourceMap0873_checked fusedMap0873_checked
    DegreeOneSmallComparisons.comparison0873
#print axioms sourceMap0873_checked
#print axioms fusedMap0873_checked
#print axioms certified0873
def sourceMap0873swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0873swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0873swap_checked : acceptsGraphIso
    (source (graph core0873) (root 8) 2 0) DegreeOneSmallSpectrum1210.graph sourceMap0873swap=true := by decide +kernel
theorem fusedMap0873swap_checked : acceptsGraphIso
    (fused (graph core0873) (root 8) 2 0) DegreeOneSmallSpectrum880.graph fusedMap0873swap=true := by decide +kernel
theorem certified0873swap : Certified (graph core0873) (root 8) 2 0 :=
  of_native_maps core0873 DegreeOneSmallSpectrum1210.graph DegreeOneSmallSpectrum880.graph
    sourceMap0873swap fusedMap0873swap sourceMap0873swap_checked fusedMap0873swap_checked
    DegreeOneSmallComparisons.comparison0873
#print axioms sourceMap0873swap_checked
#print axioms fusedMap0873swap_checked
#print axioms certified0873swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
