/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0088 : Family 8 := level8.get ⟨37,by decide⟩
def sourceMap0088 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap0088 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0088_checked : acceptsGraphIso
    (source (graph core0088) (root 8) 2 2) DegreeOneMiddleResidualSpectrum275.graph sourceMap0088=true := by decide +kernel
theorem fusedMap0088_checked : acceptsGraphIso
    (fused (graph core0088) (root 8) 2 2) DegreeTwoThreeSpectrum2317.graph fusedMap0088=true := by decide +kernel
theorem certified0088 : Certified (graph core0088) (root 8) 2 2 :=
  of_native_maps core0088 DegreeOneMiddleResidualSpectrum275.graph DegreeTwoThreeSpectrum2317.graph
    sourceMap0088 fusedMap0088 sourceMap0088_checked fusedMap0088_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0088
#print axioms sourceMap0088_checked
#print axioms fusedMap0088_checked
#print axioms certified0088
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
