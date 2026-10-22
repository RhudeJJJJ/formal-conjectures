/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0054 : Family 5 := level5.get ⟨8,by decide⟩
def sourceMap0054 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 5 2 4 v)
def fusedMap0054 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap0054_checked : acceptsGraphIso
    (source (graph core0054) (root 5) 2 4) DegreeOneMiddleResidualSpectrum073.graph sourceMap0054=true := by decide +kernel
theorem fusedMap0054_checked : acceptsGraphIso
    (fused (graph core0054) (root 5) 2 4) DegreeTwoThreeSpectrum1716.graph fusedMap0054=true := by decide +kernel
theorem certified0054 : Certified (graph core0054) (root 5) 2 4 :=
  of_native_maps core0054 DegreeOneMiddleResidualSpectrum073.graph DegreeTwoThreeSpectrum1716.graph
    sourceMap0054 fusedMap0054 sourceMap0054_checked fusedMap0054_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0054
#print axioms sourceMap0054_checked
#print axioms fusedMap0054_checked
#print axioms certified0054
def sourceMap0054swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,0,10,11,12,13,7,8,9] (sourceLabel 5 4 2 v)
def fusedMap0054swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap0054swap_checked : acceptsGraphIso
    (source (graph core0054) (root 5) 4 2) DegreeOneMiddleResidualSpectrum073.graph sourceMap0054swap=true := by decide +kernel
theorem fusedMap0054swap_checked : acceptsGraphIso
    (fused (graph core0054) (root 5) 4 2) DegreeTwoThreeSpectrum1716.graph fusedMap0054swap=true := by decide +kernel
theorem certified0054swap : Certified (graph core0054) (root 5) 4 2 :=
  of_native_maps core0054 DegreeOneMiddleResidualSpectrum073.graph DegreeTwoThreeSpectrum1716.graph
    sourceMap0054swap fusedMap0054swap sourceMap0054swap_checked fusedMap0054swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0054
#print axioms sourceMap0054swap_checked
#print axioms fusedMap0054swap_checked
#print axioms certified0054swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
