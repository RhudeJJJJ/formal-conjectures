/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0773 : Family 10 := level10.get ⟨430,by decide⟩
def sourceMap0773 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0773 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0773_checked : acceptsGraphIso
    (source (graph core0773) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1926.graph sourceMap0773=true := by decide +kernel
theorem fusedMap0773_checked : acceptsGraphIso
    (fused (graph core0773) (root 10) 2 2) DegreeTwoThreeSpectrum5830.graph fusedMap0773=true := by decide +kernel
theorem certified0773 : Certified (graph core0773) (root 10) 2 2 :=
  of_native_maps core0773 DegreeOneMiddleResidualSpectrum1926.graph DegreeTwoThreeSpectrum5830.graph
    sourceMap0773 fusedMap0773 sourceMap0773_checked fusedMap0773_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0773
#print axioms sourceMap0773_checked
#print axioms fusedMap0773_checked
#print axioms certified0773
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
