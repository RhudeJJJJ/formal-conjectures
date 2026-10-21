/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0277 : Family 6 := level6.get ⟨1,by decide⟩
def sourceMap0277 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,5,0,1,2,3,4,9,7,8] (sourceLabel 6 0 1 v)
def fusedMap0277 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0277_checked : acceptsGraphIso
    (source (graph core0277) (root 6) 0 1) DegreeOneSmallSpectrum078.graph sourceMap0277=true := by decide +kernel
theorem fusedMap0277_checked : acceptsGraphIso
    (fused (graph core0277) (root 6) 0 1) DegreeOneSmallSpectrum080.graph fusedMap0277=true := by decide +kernel
theorem certified0277 : Certified (graph core0277) (root 6) 0 1 :=
  of_native_maps core0277 DegreeOneSmallSpectrum078.graph DegreeOneSmallSpectrum080.graph
    sourceMap0277 fusedMap0277 sourceMap0277_checked fusedMap0277_checked
    DegreeOneSmallComparisons.comparison0277
#print axioms sourceMap0277_checked
#print axioms fusedMap0277_checked
#print axioms certified0277
def sourceMap0277swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,5,0,1,2,3,4,7,8,9] (sourceLabel 6 1 0 v)
def fusedMap0277swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0277swap_checked : acceptsGraphIso
    (source (graph core0277) (root 6) 1 0) DegreeOneSmallSpectrum078.graph sourceMap0277swap=true := by decide +kernel
theorem fusedMap0277swap_checked : acceptsGraphIso
    (fused (graph core0277) (root 6) 1 0) DegreeOneSmallSpectrum080.graph fusedMap0277swap=true := by decide +kernel
theorem certified0277swap : Certified (graph core0277) (root 6) 1 0 :=
  of_native_maps core0277 DegreeOneSmallSpectrum078.graph DegreeOneSmallSpectrum080.graph
    sourceMap0277swap fusedMap0277swap sourceMap0277swap_checked fusedMap0277swap_checked
    DegreeOneSmallComparisons.comparison0277
#print axioms sourceMap0277swap_checked
#print axioms fusedMap0277swap_checked
#print axioms certified0277swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
