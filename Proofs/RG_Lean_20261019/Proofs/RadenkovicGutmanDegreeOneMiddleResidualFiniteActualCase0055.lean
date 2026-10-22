/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0055 : Family 5 := level5.get ⟨9,by decide⟩
def sourceMap0055 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 5 2 4 v)
def fusedMap0055 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap0055_checked : acceptsGraphIso
    (source (graph core0055) (root 5) 2 4) DegreeOneMiddleResidualSpectrum077.graph sourceMap0055=true := by decide +kernel
theorem fusedMap0055_checked : acceptsGraphIso
    (fused (graph core0055) (root 5) 2 4) DegreeTwoThreeSpectrum1717.graph fusedMap0055=true := by decide +kernel
theorem certified0055 : Certified (graph core0055) (root 5) 2 4 :=
  of_native_maps core0055 DegreeOneMiddleResidualSpectrum077.graph DegreeTwoThreeSpectrum1717.graph
    sourceMap0055 fusedMap0055 sourceMap0055_checked fusedMap0055_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0055
#print axioms sourceMap0055_checked
#print axioms fusedMap0055_checked
#print axioms certified0055
def sourceMap0055swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,0,10,11,12,13,7,8,9] (sourceLabel 5 4 2 v)
def fusedMap0055swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap0055swap_checked : acceptsGraphIso
    (source (graph core0055) (root 5) 4 2) DegreeOneMiddleResidualSpectrum077.graph sourceMap0055swap=true := by decide +kernel
theorem fusedMap0055swap_checked : acceptsGraphIso
    (fused (graph core0055) (root 5) 4 2) DegreeTwoThreeSpectrum1717.graph fusedMap0055swap=true := by decide +kernel
theorem certified0055swap : Certified (graph core0055) (root 5) 4 2 :=
  of_native_maps core0055 DegreeOneMiddleResidualSpectrum077.graph DegreeTwoThreeSpectrum1717.graph
    sourceMap0055swap fusedMap0055swap sourceMap0055swap_checked fusedMap0055swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0055
#print axioms sourceMap0055swap_checked
#print axioms fusedMap0055swap_checked
#print axioms certified0055swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
