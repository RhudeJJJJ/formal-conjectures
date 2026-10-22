/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0197 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0197 : (Vertices 4 ⊕ Fin 5 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 4 4 4 v)
def fusedMap0197 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 4 4 v)
theorem sourceMap0197_checked : acceptsGraphIso
    (source (graph core0197) (root 4) 4 4) DegreeOneMiddleResidualSpectrum260.graph sourceMap0197=true := by decide +kernel
theorem fusedMap0197_checked : acceptsGraphIso
    (fused (graph core0197) (root 4) 4 4) DegreeTwoThreeSpectrum2320.graph fusedMap0197=true := by decide +kernel
theorem certified0197 : Certified (graph core0197) (root 4) 4 4 :=
  of_native_maps core0197 DegreeOneMiddleResidualSpectrum260.graph DegreeTwoThreeSpectrum2320.graph
    sourceMap0197 fusedMap0197 sourceMap0197_checked fusedMap0197_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0197
#print axioms sourceMap0197_checked
#print axioms fusedMap0197_checked
#print axioms certified0197
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
