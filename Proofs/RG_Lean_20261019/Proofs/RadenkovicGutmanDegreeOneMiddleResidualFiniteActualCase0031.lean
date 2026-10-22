/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0031 : Family 7 := level7.get ⟨45,by decide⟩
def sourceMap0031 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0031 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0031_checked : acceptsGraphIso
    (source (graph core0031) (root 7) 2 2) DegreeOneMiddleResidualSpectrum080.graph sourceMap0031=true := by decide +kernel
theorem fusedMap0031_checked : acceptsGraphIso
    (fused (graph core0031) (root 7) 2 2) DegreeTwoThreeSpectrum1834.graph fusedMap0031=true := by decide +kernel
theorem certified0031 : Certified (graph core0031) (root 7) 2 2 :=
  of_native_maps core0031 DegreeOneMiddleResidualSpectrum080.graph DegreeTwoThreeSpectrum1834.graph
    sourceMap0031 fusedMap0031 sourceMap0031_checked fusedMap0031_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0031
#print axioms sourceMap0031_checked
#print axioms fusedMap0031_checked
#print axioms certified0031
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
