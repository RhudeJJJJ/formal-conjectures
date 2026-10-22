/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0035 : Family 7 := level7.get ⟨52,by decide⟩
def sourceMap0035 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,1,2,3,4,5,6] (sourceLabel 7 2 2 v)
def fusedMap0035 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0035_checked : acceptsGraphIso
    (source (graph core0035) (root 7) 2 2) DegreeTwoThreeSpectrum2187.graph sourceMap0035=true := by decide +kernel
theorem fusedMap0035_checked : acceptsGraphIso
    (fused (graph core0035) (root 7) 2 2) DegreeTwoThreeSpectrum1870.graph fusedMap0035=true := by decide +kernel
theorem certified0035 : Certified (graph core0035) (root 7) 2 2 :=
  of_native_maps core0035 DegreeTwoThreeSpectrum2187.graph DegreeTwoThreeSpectrum1870.graph
    sourceMap0035 fusedMap0035 sourceMap0035_checked fusedMap0035_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0035
#print axioms sourceMap0035_checked
#print axioms fusedMap0035_checked
#print axioms certified0035
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
