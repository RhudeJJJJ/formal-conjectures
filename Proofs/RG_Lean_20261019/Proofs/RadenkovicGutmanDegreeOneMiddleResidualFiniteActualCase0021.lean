/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0021 : Family 7 := level7.get ⟨28,by decide⟩
def sourceMap0021 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0021 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0021_checked : acceptsGraphIso
    (source (graph core0021) (root 7) 2 2) DegreeOneMiddleResidualSpectrum061.graph sourceMap0021=true := by decide +kernel
theorem fusedMap0021_checked : acceptsGraphIso
    (fused (graph core0021) (root 7) 2 2) DegreeTwoThreeSpectrum1750.graph fusedMap0021=true := by decide +kernel
theorem certified0021 : Certified (graph core0021) (root 7) 2 2 :=
  of_native_maps core0021 DegreeOneMiddleResidualSpectrum061.graph DegreeTwoThreeSpectrum1750.graph
    sourceMap0021 fusedMap0021 sourceMap0021_checked fusedMap0021_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0021
#print axioms sourceMap0021_checked
#print axioms fusedMap0021_checked
#print axioms certified0021
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
