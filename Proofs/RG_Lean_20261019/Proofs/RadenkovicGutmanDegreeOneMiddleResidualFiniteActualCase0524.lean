/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0524 : Family 10 := level10.get ⟨46,by decide⟩
def sourceMap0524 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,10,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0524 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap0524_checked : acceptsGraphIso
    (source (graph core0524) (root 10) 2 2) DegreeTwoThreeSpectrum5664.graph sourceMap0524=true := by decide +kernel
theorem fusedMap0524_checked : acceptsGraphIso
    (fused (graph core0524) (root 10) 2 2) DegreeTwoThreeSpectrum5132.graph fusedMap0524=true := by decide +kernel
theorem certified0524 : Certified (graph core0524) (root 10) 2 2 :=
  of_native_maps core0524 DegreeTwoThreeSpectrum5664.graph DegreeTwoThreeSpectrum5132.graph
    sourceMap0524 fusedMap0524 sourceMap0524_checked fusedMap0524_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0524
#print axioms sourceMap0524_checked
#print axioms fusedMap0524_checked
#print axioms certified0524
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
