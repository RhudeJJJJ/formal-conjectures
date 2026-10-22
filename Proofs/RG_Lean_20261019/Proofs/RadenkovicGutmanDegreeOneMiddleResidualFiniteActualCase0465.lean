/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0465 : Family 9 := level9.get ⟨546,by decide⟩
def sourceMap0465 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0465 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0465_checked : acceptsGraphIso
    (source (graph core0465) (root 9) 2 2) DegreeOneMiddleResidualSpectrum909.graph sourceMap0465=true := by decide +kernel
theorem fusedMap0465_checked : acceptsGraphIso
    (fused (graph core0465) (root 9) 2 2) DegreeTwoThreeSpectrum4174.graph fusedMap0465=true := by decide +kernel
theorem certified0465 : Certified (graph core0465) (root 9) 2 2 :=
  of_native_maps core0465 DegreeOneMiddleResidualSpectrum909.graph DegreeTwoThreeSpectrum4174.graph
    sourceMap0465 fusedMap0465 sourceMap0465_checked fusedMap0465_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0465
#print axioms sourceMap0465_checked
#print axioms fusedMap0465_checked
#print axioms certified0465
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
