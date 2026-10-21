/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1152 : Family 8 := level8.get ⟨196,by decide⟩
def sourceMap1152 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1152 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1152_checked : acceptsGraphIso
    (source (graph core1152) (root 8) 0 1) DegreeOneSmallSpectrum629.graph sourceMap1152=true := by decide +kernel
theorem fusedMap1152_checked : acceptsGraphIso
    (fused (graph core1152) (root 8) 0 1) DegreeOneSmallSpectrum630.graph fusedMap1152=true := by decide +kernel
theorem certified1152 : Certified (graph core1152) (root 8) 0 1 :=
  of_native_maps core1152 DegreeOneSmallSpectrum629.graph DegreeOneSmallSpectrum630.graph
    sourceMap1152 fusedMap1152 sourceMap1152_checked fusedMap1152_checked
    DegreeOneSmallComparisons.comparison1152
#print axioms sourceMap1152_checked
#print axioms fusedMap1152_checked
#print axioms certified1152
def sourceMap1152swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1152swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1152swap_checked : acceptsGraphIso
    (source (graph core1152) (root 8) 1 0) DegreeOneSmallSpectrum629.graph sourceMap1152swap=true := by decide +kernel
theorem fusedMap1152swap_checked : acceptsGraphIso
    (fused (graph core1152) (root 8) 1 0) DegreeOneSmallSpectrum630.graph fusedMap1152swap=true := by decide +kernel
theorem certified1152swap : Certified (graph core1152) (root 8) 1 0 :=
  of_native_maps core1152 DegreeOneSmallSpectrum629.graph DegreeOneSmallSpectrum630.graph
    sourceMap1152swap fusedMap1152swap sourceMap1152swap_checked fusedMap1152swap_checked
    DegreeOneSmallComparisons.comparison1152
#print axioms sourceMap1152swap_checked
#print axioms fusedMap1152swap_checked
#print axioms certified1152swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
