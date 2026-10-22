/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0690 : Family 10 := level10.get ⟨292,by decide⟩
def sourceMap0690 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0690 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0690_checked : acceptsGraphIso
    (source (graph core0690) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1738.graph sourceMap0690=true := by decide +kernel
theorem fusedMap0690_checked : acceptsGraphIso
    (fused (graph core0690) (root 10) 2 2) DegreeTwoThreeSpectrum5453.graph fusedMap0690=true := by decide +kernel
theorem certified0690 : Certified (graph core0690) (root 10) 2 2 :=
  of_native_maps core0690 DegreeOneMiddleResidualSpectrum1738.graph DegreeTwoThreeSpectrum5453.graph
    sourceMap0690 fusedMap0690 sourceMap0690_checked fusedMap0690_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0690
#print axioms sourceMap0690_checked
#print axioms fusedMap0690_checked
#print axioms certified0690
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
