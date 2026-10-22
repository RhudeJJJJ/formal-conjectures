/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1028 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap1028 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,5,6,7,8,3,4,1,2] (sourceLabel 5 0 1 v)
def fusedMap1028 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,8,5,6,7] (fusedLabel 5 0 1 v)
theorem sourceMap1028_checked : acceptsGraphIso
    (source (graph core1028) (root 5) 0 1) DegreeOneSmallSpectrum057.graph sourceMap1028=true := by decide +kernel
theorem fusedMap1028_checked : acceptsGraphIso
    (fused (graph core1028) (root 5) 0 1) DegreeOneSmallSpectrum060.graph fusedMap1028=true := by decide +kernel
theorem certified1028 : Certified (graph core1028) (root 5) 0 1 :=
  of_native_maps core1028 DegreeOneSmallSpectrum057.graph DegreeOneSmallSpectrum060.graph
    sourceMap1028 fusedMap1028 sourceMap1028_checked fusedMap1028_checked
    DegreeTwoThreeFiniteComparisons.comparison1028
#print axioms sourceMap1028_checked
#print axioms fusedMap1028_checked
#print axioms certified1028
def sourceMap1028swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,5,6,7,8,3,1,2,4] (sourceLabel 5 1 0 v)
def fusedMap1028swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,8,5,6,7] (fusedLabel 5 1 0 v)
theorem sourceMap1028swap_checked : acceptsGraphIso
    (source (graph core1028) (root 5) 1 0) DegreeOneSmallSpectrum057.graph sourceMap1028swap=true := by decide +kernel
theorem fusedMap1028swap_checked : acceptsGraphIso
    (fused (graph core1028) (root 5) 1 0) DegreeOneSmallSpectrum060.graph fusedMap1028swap=true := by decide +kernel
theorem certified1028swap : Certified (graph core1028) (root 5) 1 0 :=
  of_native_maps core1028 DegreeOneSmallSpectrum057.graph DegreeOneSmallSpectrum060.graph
    sourceMap1028swap fusedMap1028swap sourceMap1028swap_checked fusedMap1028swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1028
#print axioms sourceMap1028swap_checked
#print axioms fusedMap1028swap_checked
#print axioms certified1028swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
