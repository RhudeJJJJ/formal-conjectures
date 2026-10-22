/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0189 : Family 6 := level6.get ⟨22,by decide⟩
def sourceMap0189 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap0189 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0189_checked : acceptsGraphIso
    (source (graph core0189) (root 6) 2 4) DegreeOneMiddleResidualSpectrum278.graph sourceMap0189=true := by decide +kernel
theorem fusedMap0189_checked : acceptsGraphIso
    (fused (graph core0189) (root 6) 2 4) DegreeTwoThreeSpectrum2321.graph fusedMap0189=true := by decide +kernel
theorem certified0189 : Certified (graph core0189) (root 6) 2 4 :=
  of_native_maps core0189 DegreeOneMiddleResidualSpectrum278.graph DegreeTwoThreeSpectrum2321.graph
    sourceMap0189 fusedMap0189 sourceMap0189_checked fusedMap0189_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0189
#print axioms sourceMap0189_checked
#print axioms fusedMap0189_checked
#print axioms certified0189
def sourceMap0189swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,11,12,13,14,8,9,10] (sourceLabel 6 4 2 v)
def fusedMap0189swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0189swap_checked : acceptsGraphIso
    (source (graph core0189) (root 6) 4 2) DegreeOneMiddleResidualSpectrum278.graph sourceMap0189swap=true := by decide +kernel
theorem fusedMap0189swap_checked : acceptsGraphIso
    (fused (graph core0189) (root 6) 4 2) DegreeTwoThreeSpectrum2321.graph fusedMap0189swap=true := by decide +kernel
theorem certified0189swap : Certified (graph core0189) (root 6) 4 2 :=
  of_native_maps core0189 DegreeOneMiddleResidualSpectrum278.graph DegreeTwoThreeSpectrum2321.graph
    sourceMap0189swap fusedMap0189swap sourceMap0189swap_checked fusedMap0189swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0189
#print axioms sourceMap0189swap_checked
#print axioms fusedMap0189swap_checked
#print axioms certified0189swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
