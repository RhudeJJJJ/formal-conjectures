/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1147 : Family 8 := level8.get ⟨165,by decide⟩
def sourceMap1147 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1147 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1147_checked : acceptsGraphIso
    (source (graph core1147) (root 8) 0 2) DegreeOneSmallSpectrum1473.graph sourceMap1147=true := by decide +kernel
theorem fusedMap1147_checked : acceptsGraphIso
    (fused (graph core1147) (root 8) 0 2) DegreeOneSmallSpectrum1475.graph fusedMap1147=true := by decide +kernel
theorem certified1147 : Certified (graph core1147) (root 8) 0 2 :=
  of_native_maps core1147 DegreeOneSmallSpectrum1473.graph DegreeOneSmallSpectrum1475.graph
    sourceMap1147 fusedMap1147 sourceMap1147_checked fusedMap1147_checked
    DegreeTwoThreeFiniteComparisons.comparison1147
#print axioms sourceMap1147_checked
#print axioms fusedMap1147_checked
#print axioms certified1147
def sourceMap1147swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1147swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1147swap_checked : acceptsGraphIso
    (source (graph core1147) (root 8) 2 0) DegreeOneSmallSpectrum1473.graph sourceMap1147swap=true := by decide +kernel
theorem fusedMap1147swap_checked : acceptsGraphIso
    (fused (graph core1147) (root 8) 2 0) DegreeOneSmallSpectrum1475.graph fusedMap1147swap=true := by decide +kernel
theorem certified1147swap : Certified (graph core1147) (root 8) 2 0 :=
  of_native_maps core1147 DegreeOneSmallSpectrum1473.graph DegreeOneSmallSpectrum1475.graph
    sourceMap1147swap fusedMap1147swap sourceMap1147swap_checked fusedMap1147swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1147
#print axioms sourceMap1147swap_checked
#print axioms fusedMap1147swap_checked
#print axioms certified1147swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
