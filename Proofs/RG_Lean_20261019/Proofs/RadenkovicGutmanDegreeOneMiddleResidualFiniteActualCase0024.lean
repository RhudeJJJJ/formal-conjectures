/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0024 : Family 7 := level7.get ⟨32,by decide⟩
def sourceMap0024 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0024 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0024_checked : acceptsGraphIso
    (source (graph core0024) (root 7) 2 2) DegreeOneMiddleResidualSpectrum066.graph sourceMap0024=true := by decide +kernel
theorem fusedMap0024_checked : acceptsGraphIso
    (fused (graph core0024) (root 7) 2 2) DegreeTwoThreeSpectrum1768.graph fusedMap0024=true := by decide +kernel
theorem certified0024 : Certified (graph core0024) (root 7) 2 2 :=
  of_native_maps core0024 DegreeOneMiddleResidualSpectrum066.graph DegreeTwoThreeSpectrum1768.graph
    sourceMap0024 fusedMap0024 sourceMap0024_checked fusedMap0024_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0024
#print axioms sourceMap0024_checked
#print axioms fusedMap0024_checked
#print axioms certified0024
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
