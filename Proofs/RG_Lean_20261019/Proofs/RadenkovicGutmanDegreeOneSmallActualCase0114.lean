/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0114 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0114 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 4 0 3 v)
def fusedMap0114 : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 0 3 v)
theorem sourceMap0114_checked : acceptsGraphIso
    (source (graph core0114) (root 4) 0 3) DegreeOneSmallSpectrum076.graph sourceMap0114=true := by decide +kernel
theorem fusedMap0114_checked : acceptsGraphIso
    (fused (graph core0114) (root 4) 0 3) DegreeOneSmallSpectrum080.graph fusedMap0114=true := by decide +kernel
theorem certified0114 : Certified (graph core0114) (root 4) 0 3 :=
  of_native_maps core0114 DegreeOneSmallSpectrum076.graph DegreeOneSmallSpectrum080.graph
    sourceMap0114 fusedMap0114 sourceMap0114_checked fusedMap0114_checked
    DegreeOneSmallComparisons.comparison0114
#print axioms sourceMap0114_checked
#print axioms fusedMap0114_checked
#print axioms certified0114
def sourceMap0114swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,6,7,8,9,5] (sourceLabel 4 3 0 v)
def fusedMap0114swap : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 3 0 v)
theorem sourceMap0114swap_checked : acceptsGraphIso
    (source (graph core0114) (root 4) 3 0) DegreeOneSmallSpectrum076.graph sourceMap0114swap=true := by decide +kernel
theorem fusedMap0114swap_checked : acceptsGraphIso
    (fused (graph core0114) (root 4) 3 0) DegreeOneSmallSpectrum080.graph fusedMap0114swap=true := by decide +kernel
theorem certified0114swap : Certified (graph core0114) (root 4) 3 0 :=
  of_native_maps core0114 DegreeOneSmallSpectrum076.graph DegreeOneSmallSpectrum080.graph
    sourceMap0114swap fusedMap0114swap sourceMap0114swap_checked fusedMap0114swap_checked
    DegreeOneSmallComparisons.comparison0114
#print axioms sourceMap0114swap_checked
#print axioms fusedMap0114swap_checked
#print axioms certified0114swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
