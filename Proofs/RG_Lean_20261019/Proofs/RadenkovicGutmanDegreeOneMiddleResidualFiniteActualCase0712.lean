/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0712 : Family 10 := level10.get ⟨325,by decide⟩
def sourceMap0712 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0712 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0712_checked : acceptsGraphIso
    (source (graph core0712) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1794.graph sourceMap0712=true := by decide +kernel
theorem fusedMap0712_checked : acceptsGraphIso
    (fused (graph core0712) (root 10) 2 2) DegreeTwoThreeSpectrum5552.graph fusedMap0712=true := by decide +kernel
theorem certified0712 : Certified (graph core0712) (root 10) 2 2 :=
  of_native_maps core0712 DegreeOneMiddleResidualSpectrum1794.graph DegreeTwoThreeSpectrum5552.graph
    sourceMap0712 fusedMap0712 sourceMap0712_checked fusedMap0712_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0712
#print axioms sourceMap0712_checked
#print axioms fusedMap0712_checked
#print axioms certified0712
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
