/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0762 : Family 10 := level10.get ⟨406,by decide⟩
def sourceMap0762 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0762 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0762_checked : acceptsGraphIso
    (source (graph core0762) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1882.graph sourceMap0762=true := by decide +kernel
theorem fusedMap0762_checked : acceptsGraphIso
    (fused (graph core0762) (root 10) 2 2) DegreeTwoThreeSpectrum5774.graph fusedMap0762=true := by decide +kernel
theorem certified0762 : Certified (graph core0762) (root 10) 2 2 :=
  of_native_maps core0762 DegreeOneMiddleResidualSpectrum1882.graph DegreeTwoThreeSpectrum5774.graph
    sourceMap0762 fusedMap0762 sourceMap0762_checked fusedMap0762_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0762
#print axioms sourceMap0762_checked
#print axioms fusedMap0762_checked
#print axioms certified0762
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
