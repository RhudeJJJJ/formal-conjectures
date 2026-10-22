/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0061 : Family 8 := level8.get ⟨2,by decide⟩
def sourceMap0061 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0061 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0061_checked : acceptsGraphIso
    (source (graph core0061) (root 8) 2 2) DegreeOneMiddleResidualSpectrum232.graph sourceMap0061=true := by decide +kernel
theorem fusedMap0061_checked : acceptsGraphIso
    (fused (graph core0061) (root 8) 2 2) DegreeTwoThreeSpectrum2310.graph fusedMap0061=true := by decide +kernel
theorem certified0061 : Certified (graph core0061) (root 8) 2 2 :=
  of_native_maps core0061 DegreeOneMiddleResidualSpectrum232.graph DegreeTwoThreeSpectrum2310.graph
    sourceMap0061 fusedMap0061 sourceMap0061_checked fusedMap0061_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0061
#print axioms sourceMap0061_checked
#print axioms fusedMap0061_checked
#print axioms certified0061
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
