/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0025 : Family 7 := level7.get ⟨34,by decide⟩
def sourceMap0025 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0025 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0025_checked : acceptsGraphIso
    (source (graph core0025) (root 7) 2 2) DegreeOneMiddleResidualSpectrum068.graph sourceMap0025=true := by decide +kernel
theorem fusedMap0025_checked : acceptsGraphIso
    (fused (graph core0025) (root 7) 2 2) DegreeTwoThreeSpectrum1779.graph fusedMap0025=true := by decide +kernel
theorem certified0025 : Certified (graph core0025) (root 7) 2 2 :=
  of_native_maps core0025 DegreeOneMiddleResidualSpectrum068.graph DegreeTwoThreeSpectrum1779.graph
    sourceMap0025 fusedMap0025 sourceMap0025_checked fusedMap0025_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0025
#print axioms sourceMap0025_checked
#print axioms fusedMap0025_checked
#print axioms certified0025
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
