/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0774 : Family 10 := level10.get ⟨431,by decide⟩
def sourceMap0774 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0774 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0774_checked : acceptsGraphIso
    (source (graph core0774) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1927.graph sourceMap0774=true := by decide +kernel
theorem fusedMap0774_checked : acceptsGraphIso
    (fused (graph core0774) (root 10) 2 2) DegreeTwoThreeSpectrum5833.graph fusedMap0774=true := by decide +kernel
theorem certified0774 : Certified (graph core0774) (root 10) 2 2 :=
  of_native_maps core0774 DegreeOneMiddleResidualSpectrum1927.graph DegreeTwoThreeSpectrum5833.graph
    sourceMap0774 fusedMap0774 sourceMap0774_checked fusedMap0774_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0774
#print axioms sourceMap0774_checked
#print axioms fusedMap0774_checked
#print axioms certified0774
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
