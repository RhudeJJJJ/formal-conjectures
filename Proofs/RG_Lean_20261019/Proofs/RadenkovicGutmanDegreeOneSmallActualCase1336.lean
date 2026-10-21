/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1336 : Family 9 := level9.get ⟨93,by decide⟩
def sourceMap1336 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1336 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1336_checked : acceptsGraphIso
    (source (graph core1336) (root 9) 0 1) DegreeOneSmallSpectrum1439.graph sourceMap1336=true := by decide +kernel
theorem fusedMap1336_checked : acceptsGraphIso
    (fused (graph core1336) (root 9) 0 1) DegreeOneSmallSpectrum945.graph fusedMap1336=true := by decide +kernel
theorem certified1336 : Certified (graph core1336) (root 9) 0 1 :=
  of_native_maps core1336 DegreeOneSmallSpectrum1439.graph DegreeOneSmallSpectrum945.graph
    sourceMap1336 fusedMap1336 sourceMap1336_checked fusedMap1336_checked
    DegreeOneSmallComparisons.comparison1336
#print axioms sourceMap1336_checked
#print axioms fusedMap1336_checked
#print axioms certified1336
def sourceMap1336swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1336swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1336swap_checked : acceptsGraphIso
    (source (graph core1336) (root 9) 1 0) DegreeOneSmallSpectrum1439.graph sourceMap1336swap=true := by decide +kernel
theorem fusedMap1336swap_checked : acceptsGraphIso
    (fused (graph core1336) (root 9) 1 0) DegreeOneSmallSpectrum945.graph fusedMap1336swap=true := by decide +kernel
theorem certified1336swap : Certified (graph core1336) (root 9) 1 0 :=
  of_native_maps core1336 DegreeOneSmallSpectrum1439.graph DegreeOneSmallSpectrum945.graph
    sourceMap1336swap fusedMap1336swap sourceMap1336swap_checked fusedMap1336swap_checked
    DegreeOneSmallComparisons.comparison1336
#print axioms sourceMap1336swap_checked
#print axioms fusedMap1336swap_checked
#print axioms certified1336swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
