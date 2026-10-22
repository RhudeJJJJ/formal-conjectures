/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0736 : Family 10 := level10.get ⟨368,by decide⟩
def sourceMap0736 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0736 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0736_checked : acceptsGraphIso
    (source (graph core0736) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1874.graph sourceMap0736=true := by decide +kernel
theorem fusedMap0736_checked : acceptsGraphIso
    (fused (graph core0736) (root 10) 2 2) DegreeTwoThreeSpectrum5665.graph fusedMap0736=true := by decide +kernel
theorem certified0736 : Certified (graph core0736) (root 10) 2 2 :=
  of_native_maps core0736 DegreeOneMiddleResidualSpectrum1874.graph DegreeTwoThreeSpectrum5665.graph
    sourceMap0736 fusedMap0736 sourceMap0736_checked fusedMap0736_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0736
#print axioms sourceMap0736_checked
#print axioms fusedMap0736_checked
#print axioms certified0736
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
