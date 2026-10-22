/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0916 : Family 10 := level10.get ⟨708,by decide⟩
def sourceMap0916 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0916 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0916_checked : acceptsGraphIso
    (source (graph core0916) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2179.graph sourceMap0916=true := by decide +kernel
theorem fusedMap0916_checked : acceptsGraphIso
    (fused (graph core0916) (root 10) 2 2) DegreeTwoThreeSpectrum5450.graph fusedMap0916=true := by decide +kernel
theorem certified0916 : Certified (graph core0916) (root 10) 2 2 :=
  of_native_maps core0916 DegreeOneMiddleResidualSpectrum2179.graph DegreeTwoThreeSpectrum5450.graph
    sourceMap0916 fusedMap0916 sourceMap0916_checked fusedMap0916_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0916
#print axioms sourceMap0916_checked
#print axioms fusedMap0916_checked
#print axioms certified0916
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
