/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1676 : Family 9 := level9.get ⟨438,by decide⟩
def sourceMap1676 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1676 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1676_checked : acceptsGraphIso
    (source (graph core1676) (root 9) 0 1) DegreeOneSmallSpectrum1935.graph sourceMap1676=true := by decide +kernel
theorem fusedMap1676_checked : acceptsGraphIso
    (fused (graph core1676) (root 9) 0 1) DegreeOneSmallSpectrum1349.graph fusedMap1676=true := by decide +kernel
theorem certified1676 : Certified (graph core1676) (root 9) 0 1 :=
  of_native_maps core1676 DegreeOneSmallSpectrum1935.graph DegreeOneSmallSpectrum1349.graph
    sourceMap1676 fusedMap1676 sourceMap1676_checked fusedMap1676_checked
    DegreeOneSmallComparisons.comparison1676
#print axioms sourceMap1676_checked
#print axioms fusedMap1676_checked
#print axioms certified1676
def sourceMap1676swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1676swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1676swap_checked : acceptsGraphIso
    (source (graph core1676) (root 9) 1 0) DegreeOneSmallSpectrum1935.graph sourceMap1676swap=true := by decide +kernel
theorem fusedMap1676swap_checked : acceptsGraphIso
    (fused (graph core1676) (root 9) 1 0) DegreeOneSmallSpectrum1349.graph fusedMap1676swap=true := by decide +kernel
theorem certified1676swap : Certified (graph core1676) (root 9) 1 0 :=
  of_native_maps core1676 DegreeOneSmallSpectrum1935.graph DegreeOneSmallSpectrum1349.graph
    sourceMap1676swap fusedMap1676swap sourceMap1676swap_checked fusedMap1676swap_checked
    DegreeOneSmallComparisons.comparison1676
#print axioms sourceMap1676swap_checked
#print axioms fusedMap1676swap_checked
#print axioms certified1676swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
