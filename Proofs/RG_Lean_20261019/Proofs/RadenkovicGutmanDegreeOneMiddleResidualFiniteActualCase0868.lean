/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0868 : Family 10 := level10.get ⟨605,by decide⟩
def sourceMap0868 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0868 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0868_checked : acceptsGraphIso
    (source (graph core0868) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2098.graph sourceMap0868=true := by decide +kernel
theorem fusedMap0868_checked : acceptsGraphIso
    (fused (graph core0868) (root 10) 2 2) DegreeTwoThreeSpectrum5284.graph fusedMap0868=true := by decide +kernel
theorem certified0868 : Certified (graph core0868) (root 10) 2 2 :=
  of_native_maps core0868 DegreeOneMiddleResidualSpectrum2098.graph DegreeTwoThreeSpectrum5284.graph
    sourceMap0868 fusedMap0868 sourceMap0868_checked fusedMap0868_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0868
#print axioms sourceMap0868_checked
#print axioms fusedMap0868_checked
#print axioms certified0868
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
