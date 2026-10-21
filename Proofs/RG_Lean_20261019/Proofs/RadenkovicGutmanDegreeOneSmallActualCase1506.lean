/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1506 : Family 9 := level9.get ⟨234,by decide⟩
def sourceMap1506 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1506 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 0 1 v)
theorem sourceMap1506_checked : acceptsGraphIso
    (source (graph core1506) (root 9) 0 1) DegreeOneSmallSpectrum1409.graph sourceMap1506=true := by decide +kernel
theorem fusedMap1506_checked : acceptsGraphIso
    (fused (graph core1506) (root 9) 0 1) DegreeOneSmallSpectrum1434.graph fusedMap1506=true := by decide +kernel
theorem certified1506 : Certified (graph core1506) (root 9) 0 1 :=
  of_native_maps core1506 DegreeOneSmallSpectrum1409.graph DegreeOneSmallSpectrum1434.graph
    sourceMap1506 fusedMap1506 sourceMap1506_checked fusedMap1506_checked
    DegreeOneSmallComparisons.comparison1506
#print axioms sourceMap1506_checked
#print axioms fusedMap1506_checked
#print axioms certified1506
def sourceMap1506swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1506swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (fusedLabel 9 1 0 v)
theorem sourceMap1506swap_checked : acceptsGraphIso
    (source (graph core1506) (root 9) 1 0) DegreeOneSmallSpectrum1409.graph sourceMap1506swap=true := by decide +kernel
theorem fusedMap1506swap_checked : acceptsGraphIso
    (fused (graph core1506) (root 9) 1 0) DegreeOneSmallSpectrum1434.graph fusedMap1506swap=true := by decide +kernel
theorem certified1506swap : Certified (graph core1506) (root 9) 1 0 :=
  of_native_maps core1506 DegreeOneSmallSpectrum1409.graph DegreeOneSmallSpectrum1434.graph
    sourceMap1506swap fusedMap1506swap sourceMap1506swap_checked fusedMap1506swap_checked
    DegreeOneSmallComparisons.comparison1506
#print axioms sourceMap1506swap_checked
#print axioms fusedMap1506swap_checked
#print axioms certified1506swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
