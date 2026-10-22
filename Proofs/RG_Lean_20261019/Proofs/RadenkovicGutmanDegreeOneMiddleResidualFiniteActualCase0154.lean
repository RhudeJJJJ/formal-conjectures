/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0154 : Family 8 := level8.get ⟨163,by decide⟩
def sourceMap0154 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,7,8,9,10,11,12,13,14,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap0154 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0154_checked : acceptsGraphIso
    (source (graph core0154) (root 8) 2 2) DegreeOneMiddleResidualSpectrum326.graph sourceMap0154=true := by decide +kernel
theorem fusedMap0154_checked : acceptsGraphIso
    (fused (graph core0154) (root 8) 2 2) DegreeTwoThreeSpectrum2829.graph fusedMap0154=true := by decide +kernel
theorem certified0154 : Certified (graph core0154) (root 8) 2 2 :=
  of_native_maps core0154 DegreeOneMiddleResidualSpectrum326.graph DegreeTwoThreeSpectrum2829.graph
    sourceMap0154 fusedMap0154 sourceMap0154_checked fusedMap0154_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0154
#print axioms sourceMap0154_checked
#print axioms fusedMap0154_checked
#print axioms certified0154
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
