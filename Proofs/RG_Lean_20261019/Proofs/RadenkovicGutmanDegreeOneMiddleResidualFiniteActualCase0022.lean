/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0022 : Family 7 := level7.get ⟨30,by decide⟩
def sourceMap0022 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0022 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0022_checked : acceptsGraphIso
    (source (graph core0022) (root 7) 2 2) DegreeOneMiddleResidualSpectrum063.graph sourceMap0022=true := by decide +kernel
theorem fusedMap0022_checked : acceptsGraphIso
    (fused (graph core0022) (root 7) 2 2) DegreeTwoThreeSpectrum1761.graph fusedMap0022=true := by decide +kernel
theorem certified0022 : Certified (graph core0022) (root 7) 2 2 :=
  of_native_maps core0022 DegreeOneMiddleResidualSpectrum063.graph DegreeTwoThreeSpectrum1761.graph
    sourceMap0022 fusedMap0022 sourceMap0022_checked fusedMap0022_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0022
#print axioms sourceMap0022_checked
#print axioms fusedMap0022_checked
#print axioms certified0022
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
