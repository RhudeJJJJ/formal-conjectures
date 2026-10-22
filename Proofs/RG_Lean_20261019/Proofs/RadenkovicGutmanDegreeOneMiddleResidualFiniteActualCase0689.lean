/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0689 : Family 10 := level10.get ⟨291,by decide⟩
def sourceMap0689 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0689 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0689_checked : acceptsGraphIso
    (source (graph core0689) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1737.graph sourceMap0689=true := by decide +kernel
theorem fusedMap0689_checked : acceptsGraphIso
    (fused (graph core0689) (root 10) 2 2) DegreeTwoThreeSpectrum5449.graph fusedMap0689=true := by decide +kernel
theorem certified0689 : Certified (graph core0689) (root 10) 2 2 :=
  of_native_maps core0689 DegreeOneMiddleResidualSpectrum1737.graph DegreeTwoThreeSpectrum5449.graph
    sourceMap0689 fusedMap0689 sourceMap0689_checked fusedMap0689_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0689
#print axioms sourceMap0689_checked
#print axioms fusedMap0689_checked
#print axioms certified0689
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
