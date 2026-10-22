/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0585 : Family 10 := level10.get ⟨128,by decide⟩
def sourceMap0585 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0585 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0585_checked : acceptsGraphIso
    (source (graph core0585) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1914.graph sourceMap0585=true := by decide +kernel
theorem fusedMap0585_checked : acceptsGraphIso
    (fused (graph core0585) (root 10) 2 2) DegreeTwoThreeSpectrum5057.graph fusedMap0585=true := by decide +kernel
theorem certified0585 : Certified (graph core0585) (root 10) 2 2 :=
  of_native_maps core0585 DegreeOneMiddleResidualSpectrum1914.graph DegreeTwoThreeSpectrum5057.graph
    sourceMap0585 fusedMap0585 sourceMap0585_checked fusedMap0585_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0585
#print axioms sourceMap0585_checked
#print axioms fusedMap0585_checked
#print axioms certified0585
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
