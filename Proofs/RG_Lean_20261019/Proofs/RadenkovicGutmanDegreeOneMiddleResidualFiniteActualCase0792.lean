/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0792 : Family 10 := level10.get ⟨467,by decide⟩
def sourceMap0792 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,8,9,10,11,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0792 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0792_checked : acceptsGraphIso
    (source (graph core0792) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1837.graph sourceMap0792=true := by decide +kernel
theorem fusedMap0792_checked : acceptsGraphIso
    (fused (graph core0792) (root 10) 2 2) DegreeTwoThreeSpectrum5914.graph fusedMap0792=true := by decide +kernel
theorem certified0792 : Certified (graph core0792) (root 10) 2 2 :=
  of_native_maps core0792 DegreeOneMiddleResidualSpectrum1837.graph DegreeTwoThreeSpectrum5914.graph
    sourceMap0792 fusedMap0792 sourceMap0792_checked fusedMap0792_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0792
#print axioms sourceMap0792_checked
#print axioms fusedMap0792_checked
#print axioms certified0792
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
