/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0720 : Family 10 := level10.get ⟨335,by decide⟩
def sourceMap0720 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0720 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0720_checked : acceptsGraphIso
    (source (graph core0720) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1805.graph sourceMap0720=true := by decide +kernel
theorem fusedMap0720_checked : acceptsGraphIso
    (fused (graph core0720) (root 10) 2 2) DegreeTwoThreeSpectrum5582.graph fusedMap0720=true := by decide +kernel
theorem certified0720 : Certified (graph core0720) (root 10) 2 2 :=
  of_native_maps core0720 DegreeOneMiddleResidualSpectrum1805.graph DegreeTwoThreeSpectrum5582.graph
    sourceMap0720 fusedMap0720 sourceMap0720_checked fusedMap0720_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0720
#print axioms sourceMap0720_checked
#print axioms fusedMap0720_checked
#print axioms certified0720
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
