/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0549 : Family 10 := level10.get ⟨79,by decide⟩
def sourceMap0549 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0549 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0549_checked : acceptsGraphIso
    (source (graph core0549) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1706.graph sourceMap0549=true := by decide +kernel
theorem fusedMap0549_checked : acceptsGraphIso
    (fused (graph core0549) (root 10) 2 2) DegreeTwoThreeSpectrum4995.graph fusedMap0549=true := by decide +kernel
theorem certified0549 : Certified (graph core0549) (root 10) 2 2 :=
  of_native_maps core0549 DegreeOneMiddleResidualSpectrum1706.graph DegreeTwoThreeSpectrum4995.graph
    sourceMap0549 fusedMap0549 sourceMap0549_checked fusedMap0549_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0549
#print axioms sourceMap0549_checked
#print axioms fusedMap0549_checked
#print axioms certified0549
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
