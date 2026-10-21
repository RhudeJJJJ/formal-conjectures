/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0084 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0084 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 3 1 2 v)
def fusedMap0084 : (Vertices 3 ⊕ Fin 5) → Fin 9 :=
  fun v => ![1,2,3,4,0,5,6,7,8] (fusedLabel 3 1 2 v)
theorem sourceMap0084_checked : acceptsGraphIso
    (source (graph core0084) (root 3) 1 2) DegreeOneSmallSpectrum043.graph sourceMap0084=true := by decide +kernel
theorem fusedMap0084_checked : acceptsGraphIso
    (fused (graph core0084) (root 3) 1 2) DegreeOneSmallSpectrum034.graph fusedMap0084=true := by decide +kernel
theorem certified0084 : Certified (graph core0084) (root 3) 1 2 :=
  of_native_maps core0084 DegreeOneSmallSpectrum043.graph DegreeOneSmallSpectrum034.graph
    sourceMap0084 fusedMap0084 sourceMap0084_checked fusedMap0084_checked
    DegreeOneSmallComparisons.comparison0084
#print axioms sourceMap0084_checked
#print axioms fusedMap0084_checked
#print axioms certified0084
def sourceMap0084swap : (Vertices 3 ⊕ Fin 3 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,6,7,8,4,5] (sourceLabel 3 2 1 v)
def fusedMap0084swap : (Vertices 3 ⊕ Fin 5) → Fin 9 :=
  fun v => ![1,2,3,4,0,5,6,7,8] (fusedLabel 3 2 1 v)
theorem sourceMap0084swap_checked : acceptsGraphIso
    (source (graph core0084) (root 3) 2 1) DegreeOneSmallSpectrum043.graph sourceMap0084swap=true := by decide +kernel
theorem fusedMap0084swap_checked : acceptsGraphIso
    (fused (graph core0084) (root 3) 2 1) DegreeOneSmallSpectrum034.graph fusedMap0084swap=true := by decide +kernel
theorem certified0084swap : Certified (graph core0084) (root 3) 2 1 :=
  of_native_maps core0084 DegreeOneSmallSpectrum043.graph DegreeOneSmallSpectrum034.graph
    sourceMap0084swap fusedMap0084swap sourceMap0084swap_checked fusedMap0084swap_checked
    DegreeOneSmallComparisons.comparison0084
#print axioms sourceMap0084swap_checked
#print axioms fusedMap0084swap_checked
#print axioms certified0084swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
