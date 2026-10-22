/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0927 : Family 10 := level10.get ⟨731,by decide⟩
def sourceMap0927 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0927 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0927_checked : acceptsGraphIso
    (source (graph core0927) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2198.graph sourceMap0927=true := by decide +kernel
theorem fusedMap0927_checked : acceptsGraphIso
    (fused (graph core0927) (root 10) 2 2) DegreeTwoThreeSpectrum5487.graph fusedMap0927=true := by decide +kernel
theorem certified0927 : Certified (graph core0927) (root 10) 2 2 :=
  of_native_maps core0927 DegreeOneMiddleResidualSpectrum2198.graph DegreeTwoThreeSpectrum5487.graph
    sourceMap0927 fusedMap0927 sourceMap0927_checked fusedMap0927_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0927
#print axioms sourceMap0927_checked
#print axioms fusedMap0927_checked
#print axioms certified0927
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
