/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0103 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0103 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,6,7,8,9,4,5,1,2,3] (sourceLabel 4 1 2 v)
def fusedMap0103 : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 4 1 2 v)
theorem sourceMap0103_checked : acceptsGraphIso
    (source (graph core0103) (root 4) 1 2) DegreeOneSmallSpectrum087.graph sourceMap0103=true := by decide +kernel
theorem fusedMap0103_checked : acceptsGraphIso
    (fused (graph core0103) (root 4) 1 2) DegreeOneSmallSpectrum073.graph fusedMap0103=true := by decide +kernel
theorem certified0103 : Certified (graph core0103) (root 4) 1 2 :=
  of_native_maps core0103 DegreeOneSmallSpectrum087.graph DegreeOneSmallSpectrum073.graph
    sourceMap0103 fusedMap0103 sourceMap0103_checked fusedMap0103_checked
    DegreeOneSmallComparisons.comparison0103
#print axioms sourceMap0103_checked
#print axioms fusedMap0103_checked
#print axioms certified0103
def sourceMap0103swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,6,7,8,9,1,2,3,4,5] (sourceLabel 4 2 1 v)
def fusedMap0103swap : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 4 2 1 v)
theorem sourceMap0103swap_checked : acceptsGraphIso
    (source (graph core0103) (root 4) 2 1) DegreeOneSmallSpectrum087.graph sourceMap0103swap=true := by decide +kernel
theorem fusedMap0103swap_checked : acceptsGraphIso
    (fused (graph core0103) (root 4) 2 1) DegreeOneSmallSpectrum073.graph fusedMap0103swap=true := by decide +kernel
theorem certified0103swap : Certified (graph core0103) (root 4) 2 1 :=
  of_native_maps core0103 DegreeOneSmallSpectrum087.graph DegreeOneSmallSpectrum073.graph
    sourceMap0103swap fusedMap0103swap sourceMap0103swap_checked fusedMap0103swap_checked
    DegreeOneSmallComparisons.comparison0103
#print axioms sourceMap0103swap_checked
#print axioms fusedMap0103swap_checked
#print axioms certified0103swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
