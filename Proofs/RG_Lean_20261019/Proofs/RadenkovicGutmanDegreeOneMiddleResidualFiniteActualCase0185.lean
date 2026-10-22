/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0185 : Family 6 := level6.get ⟨14,by decide⟩
def sourceMap0185 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0185 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0185_checked : acceptsGraphIso
    (source (graph core0185) (root 6) 2 4) DegreeOneMiddleResidualSpectrum252.graph sourceMap0185=true := by decide +kernel
theorem fusedMap0185_checked : acceptsGraphIso
    (fused (graph core0185) (root 6) 2 4) DegreeTwoThreeSpectrum2387.graph fusedMap0185=true := by decide +kernel
theorem certified0185 : Certified (graph core0185) (root 6) 2 4 :=
  of_native_maps core0185 DegreeOneMiddleResidualSpectrum252.graph DegreeTwoThreeSpectrum2387.graph
    sourceMap0185 fusedMap0185 sourceMap0185_checked fusedMap0185_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0185
#print axioms sourceMap0185_checked
#print axioms fusedMap0185_checked
#print axioms certified0185
def sourceMap0185swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,7,8,9] (sourceLabel 6 4 2 v)
def fusedMap0185swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0185swap_checked : acceptsGraphIso
    (source (graph core0185) (root 6) 4 2) DegreeOneMiddleResidualSpectrum252.graph sourceMap0185swap=true := by decide +kernel
theorem fusedMap0185swap_checked : acceptsGraphIso
    (fused (graph core0185) (root 6) 4 2) DegreeTwoThreeSpectrum2387.graph fusedMap0185swap=true := by decide +kernel
theorem certified0185swap : Certified (graph core0185) (root 6) 4 2 :=
  of_native_maps core0185 DegreeOneMiddleResidualSpectrum252.graph DegreeTwoThreeSpectrum2387.graph
    sourceMap0185swap fusedMap0185swap sourceMap0185swap_checked fusedMap0185swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0185
#print axioms sourceMap0185swap_checked
#print axioms fusedMap0185swap_checked
#print axioms certified0185swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
