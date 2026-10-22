/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0277 : Family 9 := level9.get ⟨104,by decide⟩
def sourceMap0277 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0277 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0277_checked : acceptsGraphIso
    (source (graph core0277) (root 9) 2 2) DegreeOneMiddleResidualSpectrum717.graph sourceMap0277=true := by decide +kernel
theorem fusedMap0277_checked : acceptsGraphIso
    (fused (graph core0277) (root 9) 2 2) DegreeTwoThreeSpectrum4098.graph fusedMap0277=true := by decide +kernel
theorem certified0277 : Certified (graph core0277) (root 9) 2 2 :=
  of_native_maps core0277 DegreeOneMiddleResidualSpectrum717.graph DegreeTwoThreeSpectrum4098.graph
    sourceMap0277 fusedMap0277 sourceMap0277_checked fusedMap0277_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0277
#print axioms sourceMap0277_checked
#print axioms fusedMap0277_checked
#print axioms certified0277
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
