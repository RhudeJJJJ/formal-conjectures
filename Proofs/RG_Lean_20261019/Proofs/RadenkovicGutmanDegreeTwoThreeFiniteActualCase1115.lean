/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1115 : Family 8 := level8.get ⟨80,by decide⟩
def sourceMap1115 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap1115 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1115_checked : acceptsGraphIso
    (source (graph core1115) (root 8) 0 2) DegreeOneSmallSpectrum1499.graph sourceMap1115=true := by decide +kernel
theorem fusedMap1115_checked : acceptsGraphIso
    (fused (graph core1115) (root 8) 0 2) DegreeOneSmallSpectrum960.graph fusedMap1115=true := by decide +kernel
theorem certified1115 : Certified (graph core1115) (root 8) 0 2 :=
  of_native_maps core1115 DegreeOneSmallSpectrum1499.graph DegreeOneSmallSpectrum960.graph
    sourceMap1115 fusedMap1115 sourceMap1115_checked fusedMap1115_checked
    DegreeTwoThreeFiniteComparisons.comparison1115
#print axioms sourceMap1115_checked
#print axioms fusedMap1115_checked
#print axioms certified1115
def sourceMap1115swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,2,3,4,6] (sourceLabel 8 2 0 v)
def fusedMap1115swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1115swap_checked : acceptsGraphIso
    (source (graph core1115) (root 8) 2 0) DegreeOneSmallSpectrum1499.graph sourceMap1115swap=true := by decide +kernel
theorem fusedMap1115swap_checked : acceptsGraphIso
    (fused (graph core1115) (root 8) 2 0) DegreeOneSmallSpectrum960.graph fusedMap1115swap=true := by decide +kernel
theorem certified1115swap : Certified (graph core1115) (root 8) 2 0 :=
  of_native_maps core1115 DegreeOneSmallSpectrum1499.graph DegreeOneSmallSpectrum960.graph
    sourceMap1115swap fusedMap1115swap sourceMap1115swap_checked fusedMap1115swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1115
#print axioms sourceMap1115swap_checked
#print axioms fusedMap1115swap_checked
#print axioms certified1115swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
