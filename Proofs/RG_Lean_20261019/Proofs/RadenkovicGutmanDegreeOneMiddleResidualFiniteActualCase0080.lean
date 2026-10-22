/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0080 : Family 8 := level8.get ⟨25,by decide⟩
def sourceMap0080 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0080 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0080_checked : acceptsGraphIso
    (source (graph core0080) (root 8) 2 2) DegreeTwoThreeSpectrum2824.graph sourceMap0080=true := by decide +kernel
theorem fusedMap0080_checked : acceptsGraphIso
    (fused (graph core0080) (root 8) 2 2) DegreeTwoThreeSpectrum2414.graph fusedMap0080=true := by decide +kernel
theorem certified0080 : Certified (graph core0080) (root 8) 2 2 :=
  of_native_maps core0080 DegreeTwoThreeSpectrum2824.graph DegreeTwoThreeSpectrum2414.graph
    sourceMap0080 fusedMap0080 sourceMap0080_checked fusedMap0080_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0080
#print axioms sourceMap0080_checked
#print axioms fusedMap0080_checked
#print axioms certified0080
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
