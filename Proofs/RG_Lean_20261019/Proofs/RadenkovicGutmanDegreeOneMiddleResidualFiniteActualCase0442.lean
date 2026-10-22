/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0442 : Family 9 := level9.get ⟨446,by decide⟩
def sourceMap0442 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0442 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0442_checked : acceptsGraphIso
    (source (graph core0442) (root 9) 2 2) DegreeOneMiddleResidualSpectrum842.graph sourceMap0442=true := by decide +kernel
theorem fusedMap0442_checked : acceptsGraphIso
    (fused (graph core0442) (root 9) 2 2) DegreeTwoThreeSpectrum4458.graph fusedMap0442=true := by decide +kernel
theorem certified0442 : Certified (graph core0442) (root 9) 2 2 :=
  of_native_maps core0442 DegreeOneMiddleResidualSpectrum842.graph DegreeTwoThreeSpectrum4458.graph
    sourceMap0442 fusedMap0442 sourceMap0442_checked fusedMap0442_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0442
#print axioms sourceMap0442_checked
#print axioms fusedMap0442_checked
#print axioms certified0442
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
