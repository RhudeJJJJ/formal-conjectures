/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1118 : Family 8 := level8.get ⟨88,by decide⟩
def sourceMap1118 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap1118 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1118_checked : acceptsGraphIso
    (source (graph core1118) (root 8) 0 2) DegreeOneSmallSpectrum1501.graph sourceMap1118=true := by decide +kernel
theorem fusedMap1118_checked : acceptsGraphIso
    (fused (graph core1118) (root 8) 0 2) DegreeOneSmallSpectrum973.graph fusedMap1118=true := by decide +kernel
theorem certified1118 : Certified (graph core1118) (root 8) 0 2 :=
  of_native_maps core1118 DegreeOneSmallSpectrum1501.graph DegreeOneSmallSpectrum973.graph
    sourceMap1118 fusedMap1118 sourceMap1118_checked fusedMap1118_checked
    DegreeTwoThreeFiniteComparisons.comparison1118
#print axioms sourceMap1118_checked
#print axioms fusedMap1118_checked
#print axioms certified1118
def sourceMap1118swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,2,3,4,6] (sourceLabel 8 2 0 v)
def fusedMap1118swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1118swap_checked : acceptsGraphIso
    (source (graph core1118) (root 8) 2 0) DegreeOneSmallSpectrum1501.graph sourceMap1118swap=true := by decide +kernel
theorem fusedMap1118swap_checked : acceptsGraphIso
    (fused (graph core1118) (root 8) 2 0) DegreeOneSmallSpectrum973.graph fusedMap1118swap=true := by decide +kernel
theorem certified1118swap : Certified (graph core1118) (root 8) 2 0 :=
  of_native_maps core1118 DegreeOneSmallSpectrum1501.graph DegreeOneSmallSpectrum973.graph
    sourceMap1118swap fusedMap1118swap sourceMap1118swap_checked fusedMap1118swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1118
#print axioms sourceMap1118swap_checked
#print axioms fusedMap1118swap_checked
#print axioms certified1118swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
