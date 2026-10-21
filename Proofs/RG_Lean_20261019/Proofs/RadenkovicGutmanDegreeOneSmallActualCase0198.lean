/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0198 : Family 5 := level5.get ⟨3,by decide⟩
def sourceMap0198 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,10,6,7,8,9] (sourceLabel 5 0 3 v)
def fusedMap0198 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 0 3 v)
theorem sourceMap0198_checked : acceptsGraphIso
    (source (graph core0198) (root 5) 0 3) DegreeOneSmallSpectrum227.graph sourceMap0198=true := by decide +kernel
theorem fusedMap0198_checked : acceptsGraphIso
    (fused (graph core0198) (root 5) 0 3) DegreeOneSmallSpectrum166.graph fusedMap0198=true := by decide +kernel
theorem certified0198 : Certified (graph core0198) (root 5) 0 3 :=
  of_native_maps core0198 DegreeOneSmallSpectrum227.graph DegreeOneSmallSpectrum166.graph
    sourceMap0198 fusedMap0198 sourceMap0198_checked fusedMap0198_checked
    DegreeOneSmallComparisons.comparison0198
#print axioms sourceMap0198_checked
#print axioms fusedMap0198_checked
#print axioms certified0198
def sourceMap0198swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 3 0 v)
def fusedMap0198swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 3 0 v)
theorem sourceMap0198swap_checked : acceptsGraphIso
    (source (graph core0198) (root 5) 3 0) DegreeOneSmallSpectrum227.graph sourceMap0198swap=true := by decide +kernel
theorem fusedMap0198swap_checked : acceptsGraphIso
    (fused (graph core0198) (root 5) 3 0) DegreeOneSmallSpectrum166.graph fusedMap0198swap=true := by decide +kernel
theorem certified0198swap : Certified (graph core0198) (root 5) 3 0 :=
  of_native_maps core0198 DegreeOneSmallSpectrum227.graph DegreeOneSmallSpectrum166.graph
    sourceMap0198swap fusedMap0198swap sourceMap0198swap_checked fusedMap0198swap_checked
    DegreeOneSmallComparisons.comparison0198
#print axioms sourceMap0198swap_checked
#print axioms fusedMap0198swap_checked
#print axioms certified0198swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
