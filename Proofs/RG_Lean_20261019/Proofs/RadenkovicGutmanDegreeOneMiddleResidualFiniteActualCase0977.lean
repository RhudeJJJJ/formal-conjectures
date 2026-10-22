/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0977 : Family 10 := level10.get ⟨841,by decide⟩
def sourceMap0977 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0977 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0977_checked : acceptsGraphIso
    (source (graph core0977) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2273.graph sourceMap0977=true := by decide +kernel
theorem fusedMap0977_checked : acceptsGraphIso
    (fused (graph core0977) (root 10) 2 2) DegreeTwoThreeSpectrum5673.graph fusedMap0977=true := by decide +kernel
theorem certified0977 : Certified (graph core0977) (root 10) 2 2 :=
  of_native_maps core0977 DegreeOneMiddleResidualSpectrum2273.graph DegreeTwoThreeSpectrum5673.graph
    sourceMap0977 fusedMap0977 sourceMap0977_checked fusedMap0977_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0977
#print axioms sourceMap0977_checked
#print axioms fusedMap0977_checked
#print axioms certified0977
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
