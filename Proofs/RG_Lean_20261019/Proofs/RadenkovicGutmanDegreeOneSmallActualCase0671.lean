/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0671 : Family 7 := level7.get ⟨62,by decide⟩
def sourceMap0671 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0671 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0671_checked : acceptsGraphIso
    (source (graph core0671) (root 7) 0 2) SmallGeFourSpectrum128.graph sourceMap0671=true := by decide +kernel
theorem fusedMap0671_checked : acceptsGraphIso
    (fused (graph core0671) (root 7) 0 2) SmallGeFourSpectrum093.graph fusedMap0671=true := by decide +kernel
theorem certified0671 : Certified (graph core0671) (root 7) 0 2 :=
  of_native_maps core0671 SmallGeFourSpectrum128.graph SmallGeFourSpectrum093.graph
    sourceMap0671 fusedMap0671 sourceMap0671_checked fusedMap0671_checked
    DegreeOneSmallComparisons.comparison0671
#print axioms sourceMap0671_checked
#print axioms fusedMap0671_checked
#print axioms certified0671
def sourceMap0671swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0671swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0671swap_checked : acceptsGraphIso
    (source (graph core0671) (root 7) 2 0) SmallGeFourSpectrum128.graph sourceMap0671swap=true := by decide +kernel
theorem fusedMap0671swap_checked : acceptsGraphIso
    (fused (graph core0671) (root 7) 2 0) SmallGeFourSpectrum093.graph fusedMap0671swap=true := by decide +kernel
theorem certified0671swap : Certified (graph core0671) (root 7) 2 0 :=
  of_native_maps core0671 SmallGeFourSpectrum128.graph SmallGeFourSpectrum093.graph
    sourceMap0671swap fusedMap0671swap sourceMap0671swap_checked fusedMap0671swap_checked
    DegreeOneSmallComparisons.comparison0671
#print axioms sourceMap0671swap_checked
#print axioms fusedMap0671swap_checked
#print axioms certified0671swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
