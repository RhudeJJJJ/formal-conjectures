/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0060 : Family 8 := level8.get ⟨1,by decide⟩
def sourceMap0060 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0060 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0060_checked : acceptsGraphIso
    (source (graph core0060) (root 8) 2 2) DegreeOneMiddleResidualSpectrum206.graph sourceMap0060=true := by decide +kernel
theorem fusedMap0060_checked : acceptsGraphIso
    (fused (graph core0060) (root 8) 2 2) DegreeTwoThreeSpectrum2309.graph fusedMap0060=true := by decide +kernel
theorem certified0060 : Certified (graph core0060) (root 8) 2 2 :=
  of_native_maps core0060 DegreeOneMiddleResidualSpectrum206.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap0060 fusedMap0060 sourceMap0060_checked fusedMap0060_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0060
#print axioms sourceMap0060_checked
#print axioms fusedMap0060_checked
#print axioms certified0060
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
