/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1250 : Family 9 := level9.get ⟨31,by decide⟩
def sourceMap1250 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1250 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1250_checked : acceptsGraphIso
    (source (graph core1250) (root 9) 0 1) DegreeOneSmallSpectrum934.graph sourceMap1250=true := by decide +kernel
theorem fusedMap1250_checked : acceptsGraphIso
    (fused (graph core1250) (root 9) 0 1) DegreeOneSmallSpectrum976.graph fusedMap1250=true := by decide +kernel
theorem certified1250 : Certified (graph core1250) (root 9) 0 1 :=
  of_native_maps core1250 DegreeOneSmallSpectrum934.graph DegreeOneSmallSpectrum976.graph
    sourceMap1250 fusedMap1250 sourceMap1250_checked fusedMap1250_checked
    DegreeOneSmallComparisons.comparison1250
#print axioms sourceMap1250_checked
#print axioms fusedMap1250_checked
#print axioms certified1250
def sourceMap1250swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1250swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1250swap_checked : acceptsGraphIso
    (source (graph core1250) (root 9) 1 0) DegreeOneSmallSpectrum934.graph sourceMap1250swap=true := by decide +kernel
theorem fusedMap1250swap_checked : acceptsGraphIso
    (fused (graph core1250) (root 9) 1 0) DegreeOneSmallSpectrum976.graph fusedMap1250swap=true := by decide +kernel
theorem certified1250swap : Certified (graph core1250) (root 9) 1 0 :=
  of_native_maps core1250 DegreeOneSmallSpectrum934.graph DegreeOneSmallSpectrum976.graph
    sourceMap1250swap fusedMap1250swap sourceMap1250swap_checked fusedMap1250swap_checked
    DegreeOneSmallComparisons.comparison1250
#print axioms sourceMap1250swap_checked
#print axioms fusedMap1250swap_checked
#print axioms certified1250swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
