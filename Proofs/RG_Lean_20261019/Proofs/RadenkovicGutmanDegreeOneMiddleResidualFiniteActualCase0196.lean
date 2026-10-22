/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0196 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0196 : (Vertices 4 ⊕ Fin 5 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 4 4 4 v)
def fusedMap0196 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13,14] (fusedLabel 4 4 4 v)
theorem sourceMap0196_checked : acceptsGraphIso
    (source (graph core0196) (root 4) 4 4) DegreeOneMiddleResidualSpectrum259.graph sourceMap0196=true := by decide +kernel
theorem fusedMap0196_checked : acceptsGraphIso
    (fused (graph core0196) (root 4) 4 4) DegreeTwoThreeSpectrum2310.graph fusedMap0196=true := by decide +kernel
theorem certified0196 : Certified (graph core0196) (root 4) 4 4 :=
  of_native_maps core0196 DegreeOneMiddleResidualSpectrum259.graph DegreeTwoThreeSpectrum2310.graph
    sourceMap0196 fusedMap0196 sourceMap0196_checked fusedMap0196_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0196
#print axioms sourceMap0196_checked
#print axioms fusedMap0196_checked
#print axioms certified0196
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
