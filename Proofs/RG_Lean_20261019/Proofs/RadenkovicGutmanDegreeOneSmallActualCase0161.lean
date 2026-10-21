/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0161 : Family 5 := level5.get ⟨0,by decide⟩
def sourceMap0161 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,5,2,3,4] (sourceLabel 5 0 2 v)
def fusedMap0161 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4] (fusedLabel 5 0 2 v)
theorem sourceMap0161_checked : acceptsGraphIso
    (source (graph core0161) (root 5) 0 2) DegreeOneSmallSpectrum090.graph sourceMap0161=true := by decide +kernel
theorem fusedMap0161_checked : acceptsGraphIso
    (fused (graph core0161) (root 5) 0 2) DegreeOneSmallSpectrum073.graph fusedMap0161=true := by decide +kernel
theorem certified0161 : Certified (graph core0161) (root 5) 0 2 :=
  of_native_maps core0161 DegreeOneSmallSpectrum090.graph DegreeOneSmallSpectrum073.graph
    sourceMap0161 fusedMap0161 sourceMap0161_checked fusedMap0161_checked
    DegreeOneSmallComparisons.comparison0161
#print axioms sourceMap0161_checked
#print axioms fusedMap0161_checked
#print axioms certified0161
def sourceMap0161swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (sourceLabel 5 2 0 v)
def fusedMap0161swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4] (fusedLabel 5 2 0 v)
theorem sourceMap0161swap_checked : acceptsGraphIso
    (source (graph core0161) (root 5) 2 0) DegreeOneSmallSpectrum090.graph sourceMap0161swap=true := by decide +kernel
theorem fusedMap0161swap_checked : acceptsGraphIso
    (fused (graph core0161) (root 5) 2 0) DegreeOneSmallSpectrum073.graph fusedMap0161swap=true := by decide +kernel
theorem certified0161swap : Certified (graph core0161) (root 5) 2 0 :=
  of_native_maps core0161 DegreeOneSmallSpectrum090.graph DegreeOneSmallSpectrum073.graph
    sourceMap0161swap fusedMap0161swap sourceMap0161swap_checked fusedMap0161swap_checked
    DegreeOneSmallComparisons.comparison0161
#print axioms sourceMap0161swap_checked
#print axioms fusedMap0161swap_checked
#print axioms certified0161swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
