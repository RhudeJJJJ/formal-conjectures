/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1008 : Family 8 := level8.get ⟨103,by decide⟩
def sourceMap1008 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (sourceLabel 8 0 1 v)
def fusedMap1008 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1008_checked : acceptsGraphIso
    (source (graph core1008) (root 8) 0 1) DegreeOneSmallSpectrum667.graph sourceMap1008=true := by decide +kernel
theorem fusedMap1008_checked : acceptsGraphIso
    (fused (graph core1008) (root 8) 0 1) DegreeOneSmallSpectrum412.graph fusedMap1008=true := by decide +kernel
theorem certified1008 : Certified (graph core1008) (root 8) 0 1 :=
  of_native_maps core1008 DegreeOneSmallSpectrum667.graph DegreeOneSmallSpectrum412.graph
    sourceMap1008 fusedMap1008 sourceMap1008_checked fusedMap1008_checked
    DegreeOneSmallComparisons.comparison1008
#print axioms sourceMap1008_checked
#print axioms fusedMap1008_checked
#print axioms certified1008
def sourceMap1008swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 8 1 0 v)
def fusedMap1008swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1008swap_checked : acceptsGraphIso
    (source (graph core1008) (root 8) 1 0) DegreeOneSmallSpectrum667.graph sourceMap1008swap=true := by decide +kernel
theorem fusedMap1008swap_checked : acceptsGraphIso
    (fused (graph core1008) (root 8) 1 0) DegreeOneSmallSpectrum412.graph fusedMap1008swap=true := by decide +kernel
theorem certified1008swap : Certified (graph core1008) (root 8) 1 0 :=
  of_native_maps core1008 DegreeOneSmallSpectrum667.graph DegreeOneSmallSpectrum412.graph
    sourceMap1008swap fusedMap1008swap sourceMap1008swap_checked fusedMap1008swap_checked
    DegreeOneSmallComparisons.comparison1008
#print axioms sourceMap1008swap_checked
#print axioms fusedMap1008swap_checked
#print axioms certified1008swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
