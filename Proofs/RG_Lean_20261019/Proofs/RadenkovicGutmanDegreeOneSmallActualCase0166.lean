/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0166 : Family 5 := level5.get ⟨0,by decide⟩
def sourceMap0166 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,5,6,2,3,4] (sourceLabel 5 1 2 v)
def fusedMap0166 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 1 2 v)
theorem sourceMap0166_checked : acceptsGraphIso
    (source (graph core0166) (root 5) 1 2) DegreeOneSmallSpectrum222.graph sourceMap0166=true := by decide +kernel
theorem fusedMap0166_checked : acceptsGraphIso
    (fused (graph core0166) (root 5) 1 2) DegreeOneSmallSpectrum168.graph fusedMap0166=true := by decide +kernel
theorem certified0166 : Certified (graph core0166) (root 5) 1 2 :=
  of_native_maps core0166 DegreeOneSmallSpectrum222.graph DegreeOneSmallSpectrum168.graph
    sourceMap0166 fusedMap0166 sourceMap0166_checked fusedMap0166_checked
    DegreeOneSmallComparisons.comparison0166
#print axioms sourceMap0166_checked
#print axioms fusedMap0166_checked
#print axioms certified0166
def sourceMap0166swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (sourceLabel 5 2 1 v)
def fusedMap0166swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 2 1 v)
theorem sourceMap0166swap_checked : acceptsGraphIso
    (source (graph core0166) (root 5) 2 1) DegreeOneSmallSpectrum222.graph sourceMap0166swap=true := by decide +kernel
theorem fusedMap0166swap_checked : acceptsGraphIso
    (fused (graph core0166) (root 5) 2 1) DegreeOneSmallSpectrum168.graph fusedMap0166swap=true := by decide +kernel
theorem certified0166swap : Certified (graph core0166) (root 5) 2 1 :=
  of_native_maps core0166 DegreeOneSmallSpectrum222.graph DegreeOneSmallSpectrum168.graph
    sourceMap0166swap fusedMap0166swap sourceMap0166swap_checked fusedMap0166swap_checked
    DegreeOneSmallComparisons.comparison0166
#print axioms sourceMap0166swap_checked
#print axioms fusedMap0166swap_checked
#print axioms certified0166swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
