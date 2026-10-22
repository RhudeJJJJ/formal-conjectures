/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0034 : Family 7 := level7.get ⟨51,by decide⟩
def sourceMap0034 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,1,2,3,4,5,6] (sourceLabel 7 2 2 v)
def fusedMap0034 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0034_checked : acceptsGraphIso
    (source (graph core0034) (root 7) 2 2) DegreeOneMiddleResidualSpectrum085.graph sourceMap0034=true := by decide +kernel
theorem fusedMap0034_checked : acceptsGraphIso
    (fused (graph core0034) (root 7) 2 2) DegreeTwoThreeSpectrum1865.graph fusedMap0034=true := by decide +kernel
theorem certified0034 : Certified (graph core0034) (root 7) 2 2 :=
  of_native_maps core0034 DegreeOneMiddleResidualSpectrum085.graph DegreeTwoThreeSpectrum1865.graph
    sourceMap0034 fusedMap0034 sourceMap0034_checked fusedMap0034_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0034
#print axioms sourceMap0034_checked
#print axioms fusedMap0034_checked
#print axioms certified0034
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
