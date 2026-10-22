/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0379 : Family 9 := level9.get ⟨289,by decide⟩
def sourceMap0379 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0379 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0379_checked : acceptsGraphIso
    (source (graph core0379) (root 9) 2 2) DegreeOneMiddleResidualSpectrum899.graph sourceMap0379=true := by decide +kernel
theorem fusedMap0379_checked : acceptsGraphIso
    (fused (graph core0379) (root 9) 2 2) DegreeTwoThreeSpectrum4117.graph fusedMap0379=true := by decide +kernel
theorem certified0379 : Certified (graph core0379) (root 9) 2 2 :=
  of_native_maps core0379 DegreeOneMiddleResidualSpectrum899.graph DegreeTwoThreeSpectrum4117.graph
    sourceMap0379 fusedMap0379 sourceMap0379_checked fusedMap0379_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0379
#print axioms sourceMap0379_checked
#print axioms fusedMap0379_checked
#print axioms certified0379
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
