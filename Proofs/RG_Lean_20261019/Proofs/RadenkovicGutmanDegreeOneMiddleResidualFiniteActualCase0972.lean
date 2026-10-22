/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0972 : Family 10 := level10.get ⟨832,by decide⟩
def sourceMap0972 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0972 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0972_checked : acceptsGraphIso
    (source (graph core0972) (root 10) 2 2) DegreeTwoThreeSpectrum7520.graph sourceMap0972=true := by decide +kernel
theorem fusedMap0972_checked : acceptsGraphIso
    (fused (graph core0972) (root 10) 2 2) DegreeTwoThreeSpectrum5656.graph fusedMap0972=true := by decide +kernel
theorem certified0972 : Certified (graph core0972) (root 10) 2 2 :=
  of_native_maps core0972 DegreeTwoThreeSpectrum7520.graph DegreeTwoThreeSpectrum5656.graph
    sourceMap0972 fusedMap0972 sourceMap0972_checked fusedMap0972_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0972
#print axioms sourceMap0972_checked
#print axioms fusedMap0972_checked
#print axioms certified0972
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
