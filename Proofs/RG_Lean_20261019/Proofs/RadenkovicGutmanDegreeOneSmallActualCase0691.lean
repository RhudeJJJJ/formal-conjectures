/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0691 : Family 7 := level7.get ⟨66,by decide⟩
def sourceMap0691 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0691 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0691_checked : acceptsGraphIso
    (source (graph core0691) (root 7) 1 1) DegreeOneSmallSpectrum647.graph sourceMap0691=true := by decide +kernel
theorem fusedMap0691_checked : acceptsGraphIso
    (fused (graph core0691) (root 7) 1 1) DegreeOneSmallSpectrum406.graph fusedMap0691=true := by decide +kernel
theorem certified0691 : Certified (graph core0691) (root 7) 1 1 :=
  of_native_maps core0691 DegreeOneSmallSpectrum647.graph DegreeOneSmallSpectrum406.graph
    sourceMap0691 fusedMap0691 sourceMap0691_checked fusedMap0691_checked
    DegreeOneSmallComparisons.comparison0691
#print axioms sourceMap0691_checked
#print axioms fusedMap0691_checked
#print axioms certified0691
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
