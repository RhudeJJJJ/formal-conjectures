/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0685 : Family 10 := level10.get ⟨286,by decide⟩
def sourceMap0685 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0685 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0685_checked : acceptsGraphIso
    (source (graph core0685) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1725.graph sourceMap0685=true := by decide +kernel
theorem fusedMap0685_checked : acceptsGraphIso
    (fused (graph core0685) (root 10) 2 2) DegreeTwoThreeSpectrum5431.graph fusedMap0685=true := by decide +kernel
theorem certified0685 : Certified (graph core0685) (root 10) 2 2 :=
  of_native_maps core0685 DegreeOneMiddleResidualSpectrum1725.graph DegreeTwoThreeSpectrum5431.graph
    sourceMap0685 fusedMap0685 sourceMap0685_checked fusedMap0685_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0685
#print axioms sourceMap0685_checked
#print axioms fusedMap0685_checked
#print axioms certified0685
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
