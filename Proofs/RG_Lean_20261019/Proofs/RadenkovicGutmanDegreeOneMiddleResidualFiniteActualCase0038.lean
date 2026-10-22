/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0038 : Family 7 := level7.get ⟨63,by decide⟩
def sourceMap0038 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0038 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0038_checked : acceptsGraphIso
    (source (graph core0038) (root 7) 2 2) DegreeOneMiddleResidualSpectrum095.graph sourceMap0038=true := by decide +kernel
theorem fusedMap0038_checked : acceptsGraphIso
    (fused (graph core0038) (root 7) 2 2) DegreeTwoThreeSpectrum1739.graph fusedMap0038=true := by decide +kernel
theorem certified0038 : Certified (graph core0038) (root 7) 2 2 :=
  of_native_maps core0038 DegreeOneMiddleResidualSpectrum095.graph DegreeTwoThreeSpectrum1739.graph
    sourceMap0038 fusedMap0038 sourceMap0038_checked fusedMap0038_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0038
#print axioms sourceMap0038_checked
#print axioms fusedMap0038_checked
#print axioms certified0038
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
