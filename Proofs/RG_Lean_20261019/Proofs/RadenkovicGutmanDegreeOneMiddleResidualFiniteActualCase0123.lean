/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0123 : Family 8 := level8.get ⟨97,by decide⟩
def sourceMap0123 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0123 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0123_checked : acceptsGraphIso
    (source (graph core0123) (root 8) 2 2) DegreeOneMiddleResidualSpectrum265.graph sourceMap0123=true := by decide +kernel
theorem fusedMap0123_checked : acceptsGraphIso
    (fused (graph core0123) (root 8) 2 2) DegreeTwoThreeSpectrum2448.graph fusedMap0123=true := by decide +kernel
theorem certified0123 : Certified (graph core0123) (root 8) 2 2 :=
  of_native_maps core0123 DegreeOneMiddleResidualSpectrum265.graph DegreeTwoThreeSpectrum2448.graph
    sourceMap0123 fusedMap0123 sourceMap0123_checked fusedMap0123_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0123
#print axioms sourceMap0123_checked
#print axioms fusedMap0123_checked
#print axioms certified0123
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
