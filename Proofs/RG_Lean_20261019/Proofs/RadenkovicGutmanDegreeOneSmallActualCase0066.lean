/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0066 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0066 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (sourceLabel 3 1 4 v)
def fusedMap0066 : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 1 4 v)
theorem sourceMap0066_checked : acceptsGraphIso
    (source (graph core0066) (root 3) 1 4) DegreeOneSmallSpectrum222.graph sourceMap0066=true := by decide +kernel
theorem fusedMap0066_checked : acceptsGraphIso
    (fused (graph core0066) (root 3) 1 4) DegreeOneSmallSpectrum168.graph fusedMap0066=true := by decide +kernel
theorem certified0066 : Certified (graph core0066) (root 3) 1 4 :=
  of_native_maps core0066 DegreeOneSmallSpectrum222.graph DegreeOneSmallSpectrum168.graph
    sourceMap0066 fusedMap0066 sourceMap0066_checked fusedMap0066_checked
    DegreeOneSmallComparisons.comparison0066
#print axioms sourceMap0066_checked
#print axioms fusedMap0066_checked
#print axioms certified0066
def sourceMap0066swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,2,3,4,0,7,8,9,10,5,6] (sourceLabel 3 4 1 v)
def fusedMap0066swap : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 4 1 v)
theorem sourceMap0066swap_checked : acceptsGraphIso
    (source (graph core0066) (root 3) 4 1) DegreeOneSmallSpectrum222.graph sourceMap0066swap=true := by decide +kernel
theorem fusedMap0066swap_checked : acceptsGraphIso
    (fused (graph core0066) (root 3) 4 1) DegreeOneSmallSpectrum168.graph fusedMap0066swap=true := by decide +kernel
theorem certified0066swap : Certified (graph core0066) (root 3) 4 1 :=
  of_native_maps core0066 DegreeOneSmallSpectrum222.graph DegreeOneSmallSpectrum168.graph
    sourceMap0066swap fusedMap0066swap sourceMap0066swap_checked fusedMap0066swap_checked
    DegreeOneSmallComparisons.comparison0066
#print axioms sourceMap0066swap_checked
#print axioms fusedMap0066swap_checked
#print axioms certified0066swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
