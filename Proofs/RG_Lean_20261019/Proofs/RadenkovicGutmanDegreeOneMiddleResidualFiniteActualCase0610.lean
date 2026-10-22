/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0610 : Family 10 := level10.get ⟨165,by decide⟩
def sourceMap0610 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0610 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0610_checked : acceptsGraphIso
    (source (graph core0610) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1942.graph sourceMap0610=true := by decide +kernel
theorem fusedMap0610_checked : acceptsGraphIso
    (fused (graph core0610) (root 10) 2 2) DegreeTwoThreeSpectrum5107.graph fusedMap0610=true := by decide +kernel
theorem certified0610 : Certified (graph core0610) (root 10) 2 2 :=
  of_native_maps core0610 DegreeOneMiddleResidualSpectrum1942.graph DegreeTwoThreeSpectrum5107.graph
    sourceMap0610 fusedMap0610 sourceMap0610_checked fusedMap0610_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0610
#print axioms sourceMap0610_checked
#print axioms fusedMap0610_checked
#print axioms certified0610
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
