/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0095 : Family 8 := level8.get ⟨46,by decide⟩
def sourceMap0095 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap0095 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0095_checked : acceptsGraphIso
    (source (graph core0095) (root 8) 2 2) DegreeOneMiddleResidualSpectrum295.graph sourceMap0095=true := by decide +kernel
theorem fusedMap0095_checked : acceptsGraphIso
    (fused (graph core0095) (root 8) 2 2) DegreeTwoThreeSpectrum2330.graph fusedMap0095=true := by decide +kernel
theorem certified0095 : Certified (graph core0095) (root 8) 2 2 :=
  of_native_maps core0095 DegreeOneMiddleResidualSpectrum295.graph DegreeTwoThreeSpectrum2330.graph
    sourceMap0095 fusedMap0095 sourceMap0095_checked fusedMap0095_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0095
#print axioms sourceMap0095_checked
#print axioms fusedMap0095_checked
#print axioms certified0095
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
