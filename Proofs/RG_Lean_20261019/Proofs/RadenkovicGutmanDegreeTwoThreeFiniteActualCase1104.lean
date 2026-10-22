/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1104 : Family 8 := level8.get ⟨43,by decide⟩
def sourceMap1104 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1104 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1104_checked : acceptsGraphIso
    (source (graph core1104) (root 8) 0 2) DegreeOneSmallSpectrum1179.graph sourceMap1104=true := by decide +kernel
theorem fusedMap1104_checked : acceptsGraphIso
    (fused (graph core1104) (root 8) 0 2) DegreeOneSmallSpectrum878.graph fusedMap1104=true := by decide +kernel
theorem certified1104 : Certified (graph core1104) (root 8) 0 2 :=
  of_native_maps core1104 DegreeOneSmallSpectrum1179.graph DegreeOneSmallSpectrum878.graph
    sourceMap1104 fusedMap1104 sourceMap1104_checked fusedMap1104_checked
    DegreeTwoThreeFiniteComparisons.comparison1104
#print axioms sourceMap1104_checked
#print axioms fusedMap1104_checked
#print axioms certified1104
def sourceMap1104swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1104swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1104swap_checked : acceptsGraphIso
    (source (graph core1104) (root 8) 2 0) DegreeOneSmallSpectrum1179.graph sourceMap1104swap=true := by decide +kernel
theorem fusedMap1104swap_checked : acceptsGraphIso
    (fused (graph core1104) (root 8) 2 0) DegreeOneSmallSpectrum878.graph fusedMap1104swap=true := by decide +kernel
theorem certified1104swap : Certified (graph core1104) (root 8) 2 0 :=
  of_native_maps core1104 DegreeOneSmallSpectrum1179.graph DegreeOneSmallSpectrum878.graph
    sourceMap1104swap fusedMap1104swap sourceMap1104swap_checked fusedMap1104swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1104
#print axioms sourceMap1104swap_checked
#print axioms fusedMap1104swap_checked
#print axioms certified1104swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
