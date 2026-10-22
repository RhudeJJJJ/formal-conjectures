/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0093 : Family 8 := level8.get ⟨44,by decide⟩
def sourceMap0093 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0093 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0093_checked : acceptsGraphIso
    (source (graph core0093) (root 8) 2 2) DegreeOneMiddleResidualSpectrum292.graph sourceMap0093=true := by decide +kernel
theorem fusedMap0093_checked : acceptsGraphIso
    (fused (graph core0093) (root 8) 2 2) DegreeTwoThreeSpectrum2328.graph fusedMap0093=true := by decide +kernel
theorem certified0093 : Certified (graph core0093) (root 8) 2 2 :=
  of_native_maps core0093 DegreeOneMiddleResidualSpectrum292.graph DegreeTwoThreeSpectrum2328.graph
    sourceMap0093 fusedMap0093 sourceMap0093_checked fusedMap0093_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0093
#print axioms sourceMap0093_checked
#print axioms fusedMap0093_checked
#print axioms certified0093
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
