/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0874 : Family 10 := level10.get ⟨620,by decide⟩
def sourceMap0874 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0874 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0874_checked : acceptsGraphIso
    (source (graph core0874) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2112.graph sourceMap0874=true := by decide +kernel
theorem fusedMap0874_checked : acceptsGraphIso
    (fused (graph core0874) (root 10) 2 2) DegreeTwoThreeSpectrum5311.graph fusedMap0874=true := by decide +kernel
theorem certified0874 : Certified (graph core0874) (root 10) 2 2 :=
  of_native_maps core0874 DegreeOneMiddleResidualSpectrum2112.graph DegreeTwoThreeSpectrum5311.graph
    sourceMap0874 fusedMap0874 sourceMap0874_checked fusedMap0874_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0874
#print axioms sourceMap0874_checked
#print axioms fusedMap0874_checked
#print axioms certified0874
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
