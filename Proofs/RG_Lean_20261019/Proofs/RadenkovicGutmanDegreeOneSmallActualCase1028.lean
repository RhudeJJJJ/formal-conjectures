/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1028 : Family 8 := level8.get ⟨112,by decide⟩
def sourceMap1028 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1028 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1028_checked : acceptsGraphIso
    (source (graph core1028) (root 8) 0 1) DegreeOneSmallSpectrum717.graph sourceMap1028=true := by decide +kernel
theorem fusedMap1028_checked : acceptsGraphIso
    (fused (graph core1028) (root 8) 0 1) SmallGeFourSpectrum095.graph fusedMap1028=true := by decide +kernel
theorem certified1028 : Certified (graph core1028) (root 8) 0 1 :=
  of_native_maps core1028 DegreeOneSmallSpectrum717.graph SmallGeFourSpectrum095.graph
    sourceMap1028 fusedMap1028 sourceMap1028_checked fusedMap1028_checked
    DegreeOneSmallComparisons.comparison1028
#print axioms sourceMap1028_checked
#print axioms fusedMap1028_checked
#print axioms certified1028
def sourceMap1028swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1028swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1028swap_checked : acceptsGraphIso
    (source (graph core1028) (root 8) 1 0) DegreeOneSmallSpectrum717.graph sourceMap1028swap=true := by decide +kernel
theorem fusedMap1028swap_checked : acceptsGraphIso
    (fused (graph core1028) (root 8) 1 0) SmallGeFourSpectrum095.graph fusedMap1028swap=true := by decide +kernel
theorem certified1028swap : Certified (graph core1028) (root 8) 1 0 :=
  of_native_maps core1028 DegreeOneSmallSpectrum717.graph SmallGeFourSpectrum095.graph
    sourceMap1028swap fusedMap1028swap sourceMap1028swap_checked fusedMap1028swap_checked
    DegreeOneSmallComparisons.comparison1028
#print axioms sourceMap1028swap_checked
#print axioms fusedMap1028swap_checked
#print axioms certified1028swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
