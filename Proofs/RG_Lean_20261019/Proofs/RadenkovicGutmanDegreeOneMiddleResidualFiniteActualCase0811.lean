/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0811 : Family 10 := level10.get ⟨509,by decide⟩
def sourceMap0811 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0811 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0811_checked : acceptsGraphIso
    (source (graph core0811) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1986.graph sourceMap0811=true := by decide +kernel
theorem fusedMap0811_checked : acceptsGraphIso
    (fused (graph core0811) (root 10) 2 2) DegreeTwoThreeSpectrum5147.graph fusedMap0811=true := by decide +kernel
theorem certified0811 : Certified (graph core0811) (root 10) 2 2 :=
  of_native_maps core0811 DegreeOneMiddleResidualSpectrum1986.graph DegreeTwoThreeSpectrum5147.graph
    sourceMap0811 fusedMap0811 sourceMap0811_checked fusedMap0811_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0811
#print axioms sourceMap0811_checked
#print axioms fusedMap0811_checked
#print axioms certified0811
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
