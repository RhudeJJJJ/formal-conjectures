/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0018 : Family 7 := level7.get ⟨22,by decide⟩
def sourceMap0018 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,2,3,4,5,6,7] (sourceLabel 7 2 2 v)
def fusedMap0018 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0018_checked : acceptsGraphIso
    (source (graph core0018) (root 7) 2 2) DegreeOneMiddleResidualSpectrum092.graph sourceMap0018=true := by decide +kernel
theorem fusedMap0018_checked : acceptsGraphIso
    (fused (graph core0018) (root 7) 2 2) DegreeTwoThreeSpectrum1730.graph fusedMap0018=true := by decide +kernel
theorem certified0018 : Certified (graph core0018) (root 7) 2 2 :=
  of_native_maps core0018 DegreeOneMiddleResidualSpectrum092.graph DegreeTwoThreeSpectrum1730.graph
    sourceMap0018 fusedMap0018 sourceMap0018_checked fusedMap0018_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0018
#print axioms sourceMap0018_checked
#print axioms fusedMap0018_checked
#print axioms certified0018
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
