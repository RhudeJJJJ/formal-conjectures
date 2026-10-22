/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0053 : Family 5 := level5.get ⟨6,by decide⟩
def sourceMap0053 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 5 2 4 v)
def fusedMap0053 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap0053_checked : acceptsGraphIso
    (source (graph core0053) (root 5) 2 4) DegreeOneMiddleResidualSpectrum065.graph sourceMap0053=true := by decide +kernel
theorem fusedMap0053_checked : acceptsGraphIso
    (fused (graph core0053) (root 5) 2 4) DegreeTwoThreeSpectrum1710.graph fusedMap0053=true := by decide +kernel
theorem certified0053 : Certified (graph core0053) (root 5) 2 4 :=
  of_native_maps core0053 DegreeOneMiddleResidualSpectrum065.graph DegreeTwoThreeSpectrum1710.graph
    sourceMap0053 fusedMap0053 sourceMap0053_checked fusedMap0053_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0053
#print axioms sourceMap0053_checked
#print axioms fusedMap0053_checked
#print axioms certified0053
def sourceMap0053swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,0,10,11,12,13,7,8,9] (sourceLabel 5 4 2 v)
def fusedMap0053swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap0053swap_checked : acceptsGraphIso
    (source (graph core0053) (root 5) 4 2) DegreeOneMiddleResidualSpectrum065.graph sourceMap0053swap=true := by decide +kernel
theorem fusedMap0053swap_checked : acceptsGraphIso
    (fused (graph core0053) (root 5) 4 2) DegreeTwoThreeSpectrum1710.graph fusedMap0053swap=true := by decide +kernel
theorem certified0053swap : Certified (graph core0053) (root 5) 4 2 :=
  of_native_maps core0053 DegreeOneMiddleResidualSpectrum065.graph DegreeTwoThreeSpectrum1710.graph
    sourceMap0053swap fusedMap0053swap sourceMap0053swap_checked fusedMap0053swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0053
#print axioms sourceMap0053swap_checked
#print axioms fusedMap0053swap_checked
#print axioms certified0053swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
