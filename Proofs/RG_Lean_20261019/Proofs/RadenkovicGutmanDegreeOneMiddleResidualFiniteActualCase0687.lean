/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0687 : Family 10 := level10.get ⟨288,by decide⟩
def sourceMap0687 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0687 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0687_checked : acceptsGraphIso
    (source (graph core0687) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1727.graph sourceMap0687=true := by decide +kernel
theorem fusedMap0687_checked : acceptsGraphIso
    (fused (graph core0687) (root 10) 2 2) DegreeTwoThreeSpectrum5438.graph fusedMap0687=true := by decide +kernel
theorem certified0687 : Certified (graph core0687) (root 10) 2 2 :=
  of_native_maps core0687 DegreeOneMiddleResidualSpectrum1727.graph DegreeTwoThreeSpectrum5438.graph
    sourceMap0687 fusedMap0687 sourceMap0687_checked fusedMap0687_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0687
#print axioms sourceMap0687_checked
#print axioms fusedMap0687_checked
#print axioms certified0687
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
