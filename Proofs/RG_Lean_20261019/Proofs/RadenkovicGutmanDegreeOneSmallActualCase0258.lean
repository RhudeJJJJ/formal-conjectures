/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0258 : Family 5 := level5.get ⟨13,by decide⟩
def sourceMap0258 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (sourceLabel 5 0 3 v)
def fusedMap0258 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 0 3 v)
theorem sourceMap0258_checked : acceptsGraphIso
    (source (graph core0258) (root 5) 0 3) DegreeOneSmallSpectrum239.graph sourceMap0258=true := by decide +kernel
theorem fusedMap0258_checked : acceptsGraphIso
    (fused (graph core0258) (root 5) 0 3) SmallGeFourSpectrum037.graph fusedMap0258=true := by decide +kernel
theorem certified0258 : Certified (graph core0258) (root 5) 0 3 :=
  of_native_maps core0258 DegreeOneSmallSpectrum239.graph SmallGeFourSpectrum037.graph
    sourceMap0258 fusedMap0258 sourceMap0258_checked fusedMap0258_checked
    DegreeOneSmallComparisons.comparison0258
#print axioms sourceMap0258_checked
#print axioms fusedMap0258_checked
#print axioms certified0258
def sourceMap0258swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,7] (sourceLabel 5 3 0 v)
def fusedMap0258swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 3 0 v)
theorem sourceMap0258swap_checked : acceptsGraphIso
    (source (graph core0258) (root 5) 3 0) DegreeOneSmallSpectrum239.graph sourceMap0258swap=true := by decide +kernel
theorem fusedMap0258swap_checked : acceptsGraphIso
    (fused (graph core0258) (root 5) 3 0) SmallGeFourSpectrum037.graph fusedMap0258swap=true := by decide +kernel
theorem certified0258swap : Certified (graph core0258) (root 5) 3 0 :=
  of_native_maps core0258 DegreeOneSmallSpectrum239.graph SmallGeFourSpectrum037.graph
    sourceMap0258swap fusedMap0258swap sourceMap0258swap_checked fusedMap0258swap_checked
    DegreeOneSmallComparisons.comparison0258
#print axioms sourceMap0258swap_checked
#print axioms fusedMap0258swap_checked
#print axioms certified0258swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
