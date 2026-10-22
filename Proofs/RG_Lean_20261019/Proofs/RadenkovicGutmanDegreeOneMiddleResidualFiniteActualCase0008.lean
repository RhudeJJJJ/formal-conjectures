/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0008 : Family 7 := level7.get ⟨9,by decide⟩
def sourceMap0008 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0008 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0008_checked : acceptsGraphIso
    (source (graph core0008) (root 7) 2 2) DegreeOneMiddleResidualSpectrum070.graph sourceMap0008=true := by decide +kernel
theorem fusedMap0008_checked : acceptsGraphIso
    (fused (graph core0008) (root 7) 2 2) DegreeTwoThreeSpectrum1711.graph fusedMap0008=true := by decide +kernel
theorem certified0008 : Certified (graph core0008) (root 7) 2 2 :=
  of_native_maps core0008 DegreeOneMiddleResidualSpectrum070.graph DegreeTwoThreeSpectrum1711.graph
    sourceMap0008 fusedMap0008 sourceMap0008_checked fusedMap0008_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0008
#print axioms sourceMap0008_checked
#print axioms fusedMap0008_checked
#print axioms certified0008
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
