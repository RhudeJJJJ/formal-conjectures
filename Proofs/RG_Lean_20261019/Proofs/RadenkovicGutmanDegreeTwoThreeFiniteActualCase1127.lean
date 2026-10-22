/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1127 : Family 8 := level8.get ⟨114,by decide⟩
def sourceMap1127 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1127 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1127_checked : acceptsGraphIso
    (source (graph core1127) (root 8) 0 2) DegreeOneSmallSpectrum1133.graph sourceMap1127=true := by decide +kernel
theorem fusedMap1127_checked : acceptsGraphIso
    (fused (graph core1127) (root 8) 0 2) DegreeOneSmallSpectrum1135.graph fusedMap1127=true := by decide +kernel
theorem certified1127 : Certified (graph core1127) (root 8) 0 2 :=
  of_native_maps core1127 DegreeOneSmallSpectrum1133.graph DegreeOneSmallSpectrum1135.graph
    sourceMap1127 fusedMap1127 sourceMap1127_checked fusedMap1127_checked
    DegreeTwoThreeFiniteComparisons.comparison1127
#print axioms sourceMap1127_checked
#print axioms fusedMap1127_checked
#print axioms certified1127
def sourceMap1127swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1127swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1127swap_checked : acceptsGraphIso
    (source (graph core1127) (root 8) 2 0) DegreeOneSmallSpectrum1133.graph sourceMap1127swap=true := by decide +kernel
theorem fusedMap1127swap_checked : acceptsGraphIso
    (fused (graph core1127) (root 8) 2 0) DegreeOneSmallSpectrum1135.graph fusedMap1127swap=true := by decide +kernel
theorem certified1127swap : Certified (graph core1127) (root 8) 2 0 :=
  of_native_maps core1127 DegreeOneSmallSpectrum1133.graph DegreeOneSmallSpectrum1135.graph
    sourceMap1127swap fusedMap1127swap sourceMap1127swap_checked fusedMap1127swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1127
#print axioms sourceMap1127swap_checked
#print axioms fusedMap1127swap_checked
#print axioms certified1127swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
