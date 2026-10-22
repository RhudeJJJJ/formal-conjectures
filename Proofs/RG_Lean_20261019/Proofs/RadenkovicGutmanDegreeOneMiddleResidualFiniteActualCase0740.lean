/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0740 : Family 10 := level10.get ⟨373,by decide⟩
def sourceMap0740 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0740 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0740_checked : acceptsGraphIso
    (source (graph core0740) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1898.graph sourceMap0740=true := by decide +kernel
theorem fusedMap0740_checked : acceptsGraphIso
    (fused (graph core0740) (root 10) 2 2) DegreeTwoThreeSpectrum5683.graph fusedMap0740=true := by decide +kernel
theorem certified0740 : Certified (graph core0740) (root 10) 2 2 :=
  of_native_maps core0740 DegreeOneMiddleResidualSpectrum1898.graph DegreeTwoThreeSpectrum5683.graph
    sourceMap0740 fusedMap0740 sourceMap0740_checked fusedMap0740_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0740
#print axioms sourceMap0740_checked
#print axioms fusedMap0740_checked
#print axioms certified0740
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
