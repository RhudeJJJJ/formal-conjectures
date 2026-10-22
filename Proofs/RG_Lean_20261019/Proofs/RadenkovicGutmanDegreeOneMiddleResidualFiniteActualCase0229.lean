/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0229 : Family 9 := level9.get ⟨36,by decide⟩
def sourceMap0229 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,10,11,12,13,14,15,9,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap0229 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0229_checked : acceptsGraphIso
    (source (graph core0229) (root 9) 2 2) DegreeOneMiddleResidualSpectrum707.graph sourceMap0229=true := by decide +kernel
theorem fusedMap0229_checked : acceptsGraphIso
    (fused (graph core0229) (root 9) 2 2) DegreeTwoThreeSpectrum3885.graph fusedMap0229=true := by decide +kernel
theorem certified0229 : Certified (graph core0229) (root 9) 2 2 :=
  of_native_maps core0229 DegreeOneMiddleResidualSpectrum707.graph DegreeTwoThreeSpectrum3885.graph
    sourceMap0229 fusedMap0229 sourceMap0229_checked fusedMap0229_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0229
#print axioms sourceMap0229_checked
#print axioms fusedMap0229_checked
#print axioms certified0229
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
