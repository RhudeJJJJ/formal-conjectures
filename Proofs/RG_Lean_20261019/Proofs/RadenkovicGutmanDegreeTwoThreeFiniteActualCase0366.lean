/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0366 : Family 9 := level9.get ⟨594,by decide⟩
def sourceMap0366 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0366 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0366_checked : acceptsGraphIso
    (source (graph core0366) (root 9) 0 0) DegreeOneSmallSpectrum695.graph sourceMap0366=true := by decide +kernel
theorem fusedMap0366_checked : acceptsGraphIso
    (fused (graph core0366) (root 9) 0 0) DegreeOneSmallSpectrum694.graph fusedMap0366=true := by decide +kernel
theorem certified0366 : Certified (graph core0366) (root 9) 0 0 :=
  of_native_maps core0366 DegreeOneSmallSpectrum695.graph DegreeOneSmallSpectrum694.graph
    sourceMap0366 fusedMap0366 sourceMap0366_checked fusedMap0366_checked
    DegreeTwoThreeFiniteComparisons.comparison0366
#print axioms sourceMap0366_checked
#print axioms fusedMap0366_checked
#print axioms certified0366
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
