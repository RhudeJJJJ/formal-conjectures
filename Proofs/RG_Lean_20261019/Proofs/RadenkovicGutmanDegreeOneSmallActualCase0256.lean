/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0256 : Family 5 := level5.get ⟨13,by decide⟩
def sourceMap0256 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,8,6,7] (sourceLabel 5 0 1 v)
def fusedMap0256 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 0 1 v)
theorem sourceMap0256_checked : acceptsGraphIso
    (source (graph core0256) (root 5) 0 1) DegreeOneSmallSpectrum066.graph sourceMap0256=true := by decide +kernel
theorem fusedMap0256_checked : acceptsGraphIso
    (fused (graph core0256) (root 5) 0 1) SmallGeFourSpectrum006.graph fusedMap0256=true := by decide +kernel
theorem certified0256 : Certified (graph core0256) (root 5) 0 1 :=
  of_native_maps core0256 DegreeOneSmallSpectrum066.graph SmallGeFourSpectrum006.graph
    sourceMap0256 fusedMap0256 sourceMap0256_checked fusedMap0256_checked
    DegreeOneSmallComparisons.comparison0256
#print axioms sourceMap0256_checked
#print axioms fusedMap0256_checked
#print axioms certified0256
def sourceMap0256swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 5 1 0 v)
def fusedMap0256swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 1 0 v)
theorem sourceMap0256swap_checked : acceptsGraphIso
    (source (graph core0256) (root 5) 1 0) DegreeOneSmallSpectrum066.graph sourceMap0256swap=true := by decide +kernel
theorem fusedMap0256swap_checked : acceptsGraphIso
    (fused (graph core0256) (root 5) 1 0) SmallGeFourSpectrum006.graph fusedMap0256swap=true := by decide +kernel
theorem certified0256swap : Certified (graph core0256) (root 5) 1 0 :=
  of_native_maps core0256 DegreeOneSmallSpectrum066.graph SmallGeFourSpectrum006.graph
    sourceMap0256swap fusedMap0256swap sourceMap0256swap_checked fusedMap0256swap_checked
    DegreeOneSmallComparisons.comparison0256
#print axioms sourceMap0256swap_checked
#print axioms fusedMap0256swap_checked
#print axioms certified0256swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
