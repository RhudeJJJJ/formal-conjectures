/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0039 : Family 7 := level7.get ⟨65,by decide⟩
def sourceMap0039 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0039 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0039_checked : acceptsGraphIso
    (source (graph core0039) (root 7) 2 2) DegreeOneMiddleResidualSpectrum096.graph sourceMap0039=true := by decide +kernel
theorem fusedMap0039_checked : acceptsGraphIso
    (fused (graph core0039) (root 7) 2 2) DegreeTwoThreeSpectrum1742.graph fusedMap0039=true := by decide +kernel
theorem certified0039 : Certified (graph core0039) (root 7) 2 2 :=
  of_native_maps core0039 DegreeOneMiddleResidualSpectrum096.graph DegreeTwoThreeSpectrum1742.graph
    sourceMap0039 fusedMap0039 sourceMap0039_checked fusedMap0039_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0039
#print axioms sourceMap0039_checked
#print axioms fusedMap0039_checked
#print axioms certified0039
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
