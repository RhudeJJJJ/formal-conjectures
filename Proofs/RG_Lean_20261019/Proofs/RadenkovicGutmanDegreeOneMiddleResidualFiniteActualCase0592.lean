/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0592 : Family 10 := level10.get ⟨137,by decide⟩
def sourceMap0592 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0592 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0592_checked : acceptsGraphIso
    (source (graph core0592) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1923.graph sourceMap0592=true := by decide +kernel
theorem fusedMap0592_checked : acceptsGraphIso
    (fused (graph core0592) (root 10) 2 2) DegreeTwoThreeSpectrum5068.graph fusedMap0592=true := by decide +kernel
theorem certified0592 : Certified (graph core0592) (root 10) 2 2 :=
  of_native_maps core0592 DegreeOneMiddleResidualSpectrum1923.graph DegreeTwoThreeSpectrum5068.graph
    sourceMap0592 fusedMap0592 sourceMap0592_checked fusedMap0592_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0592
#print axioms sourceMap0592_checked
#print axioms fusedMap0592_checked
#print axioms certified0592
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
