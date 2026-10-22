/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0643 : Family 10 := level10.get ⟨218,by decide⟩
def sourceMap0643 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0643 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0643_checked : acceptsGraphIso
    (source (graph core0643) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1617.graph sourceMap0643=true := by decide +kernel
theorem fusedMap0643_checked : acceptsGraphIso
    (fused (graph core0643) (root 10) 2 2) DegreeTwoThreeSpectrum5241.graph fusedMap0643=true := by decide +kernel
theorem certified0643 : Certified (graph core0643) (root 10) 2 2 :=
  of_native_maps core0643 DegreeOneMiddleResidualSpectrum1617.graph DegreeTwoThreeSpectrum5241.graph
    sourceMap0643 fusedMap0643 sourceMap0643_checked fusedMap0643_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0643
#print axioms sourceMap0643_checked
#print axioms fusedMap0643_checked
#print axioms certified0643
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
