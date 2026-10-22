/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0201 : Family 9 := level9.get ⟨3,by decide⟩
def sourceMap0201 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap0201 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0201_checked : acceptsGraphIso
    (source (graph core0201) (root 9) 2 2) DegreeOneMiddleResidualSpectrum499.graph sourceMap0201=true := by decide +kernel
theorem fusedMap0201_checked : acceptsGraphIso
    (fused (graph core0201) (root 9) 2 2) DegreeTwoThreeSpectrum3876.graph fusedMap0201=true := by decide +kernel
theorem certified0201 : Certified (graph core0201) (root 9) 2 2 :=
  of_native_maps core0201 DegreeOneMiddleResidualSpectrum499.graph DegreeTwoThreeSpectrum3876.graph
    sourceMap0201 fusedMap0201 sourceMap0201_checked fusedMap0201_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0201
#print axioms sourceMap0201_checked
#print axioms fusedMap0201_checked
#print axioms certified0201
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
