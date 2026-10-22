/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0049 : Family 5 := level5.get ⟨1,by decide⟩
def sourceMap0049 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 5 2 4 v)
def fusedMap0049 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap0049_checked : acceptsGraphIso
    (source (graph core0049) (root 5) 2 4) DegreeOneMiddleResidualSpectrum034.graph sourceMap0049=true := by decide +kernel
theorem fusedMap0049_checked : acceptsGraphIso
    (fused (graph core0049) (root 5) 2 4) DegreeTwoThreeSpectrum1715.graph fusedMap0049=true := by decide +kernel
theorem certified0049 : Certified (graph core0049) (root 5) 2 4 :=
  of_native_maps core0049 DegreeOneMiddleResidualSpectrum034.graph DegreeTwoThreeSpectrum1715.graph
    sourceMap0049 fusedMap0049 sourceMap0049_checked fusedMap0049_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0049
#print axioms sourceMap0049_checked
#print axioms fusedMap0049_checked
#print axioms certified0049
def sourceMap0049swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,6,7,8] (sourceLabel 5 4 2 v)
def fusedMap0049swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap0049swap_checked : acceptsGraphIso
    (source (graph core0049) (root 5) 4 2) DegreeOneMiddleResidualSpectrum034.graph sourceMap0049swap=true := by decide +kernel
theorem fusedMap0049swap_checked : acceptsGraphIso
    (fused (graph core0049) (root 5) 4 2) DegreeTwoThreeSpectrum1715.graph fusedMap0049swap=true := by decide +kernel
theorem certified0049swap : Certified (graph core0049) (root 5) 4 2 :=
  of_native_maps core0049 DegreeOneMiddleResidualSpectrum034.graph DegreeTwoThreeSpectrum1715.graph
    sourceMap0049swap fusedMap0049swap sourceMap0049swap_checked fusedMap0049swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0049
#print axioms sourceMap0049swap_checked
#print axioms fusedMap0049swap_checked
#print axioms certified0049swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
