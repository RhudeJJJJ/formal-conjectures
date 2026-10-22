/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0730 : Family 10 := level10.get ⟨351,by decide⟩
def sourceMap0730 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0730 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0730_checked : acceptsGraphIso
    (source (graph core0730) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1820.graph sourceMap0730=true := by decide +kernel
theorem fusedMap0730_checked : acceptsGraphIso
    (fused (graph core0730) (root 10) 2 2) DegreeTwoThreeSpectrum5623.graph fusedMap0730=true := by decide +kernel
theorem certified0730 : Certified (graph core0730) (root 10) 2 2 :=
  of_native_maps core0730 DegreeOneMiddleResidualSpectrum1820.graph DegreeTwoThreeSpectrum5623.graph
    sourceMap0730 fusedMap0730 sourceMap0730_checked fusedMap0730_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0730
#print axioms sourceMap0730_checked
#print axioms fusedMap0730_checked
#print axioms certified0730
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
