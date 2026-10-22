/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0109 : Family 8 := level8.get ⟨70,by decide⟩
def sourceMap0109 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0109 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0109_checked : acceptsGraphIso
    (source (graph core0109) (root 8) 2 2) DegreeOneMiddleResidualSpectrum325.graph sourceMap0109=true := by decide +kernel
theorem fusedMap0109_checked : acceptsGraphIso
    (fused (graph core0109) (root 8) 2 2) DegreeTwoThreeSpectrum2381.graph fusedMap0109=true := by decide +kernel
theorem certified0109 : Certified (graph core0109) (root 8) 2 2 :=
  of_native_maps core0109 DegreeOneMiddleResidualSpectrum325.graph DegreeTwoThreeSpectrum2381.graph
    sourceMap0109 fusedMap0109 sourceMap0109_checked fusedMap0109_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0109
#print axioms sourceMap0109_checked
#print axioms fusedMap0109_checked
#print axioms certified0109
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
