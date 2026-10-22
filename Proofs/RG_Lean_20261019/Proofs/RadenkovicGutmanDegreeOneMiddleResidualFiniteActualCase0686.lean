/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0686 : Family 10 := level10.get ⟨287,by decide⟩
def sourceMap0686 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0686 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0686_checked : acceptsGraphIso
    (source (graph core0686) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1726.graph sourceMap0686=true := by decide +kernel
theorem fusedMap0686_checked : acceptsGraphIso
    (fused (graph core0686) (root 10) 2 2) DegreeTwoThreeSpectrum5435.graph fusedMap0686=true := by decide +kernel
theorem certified0686 : Certified (graph core0686) (root 10) 2 2 :=
  of_native_maps core0686 DegreeOneMiddleResidualSpectrum1726.graph DegreeTwoThreeSpectrum5435.graph
    sourceMap0686 fusedMap0686 sourceMap0686_checked fusedMap0686_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0686
#print axioms sourceMap0686_checked
#print axioms fusedMap0686_checked
#print axioms certified0686
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
