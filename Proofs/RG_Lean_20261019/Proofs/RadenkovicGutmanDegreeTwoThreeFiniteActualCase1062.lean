/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1062 : Family 7 := level7.get ⟨20,by decide⟩
def sourceMap1062 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 7 0 2 v)
def fusedMap1062 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (fusedLabel 7 0 2 v)
theorem sourceMap1062_checked : acceptsGraphIso
    (source (graph core1062) (root 7) 0 2) DegreeOneSmallSpectrum580.graph sourceMap1062=true := by decide +kernel
theorem fusedMap1062_checked : acceptsGraphIso
    (fused (graph core1062) (root 7) 0 2) DegreeOneSmallSpectrum391.graph fusedMap1062=true := by decide +kernel
theorem certified1062 : Certified (graph core1062) (root 7) 0 2 :=
  of_native_maps core1062 DegreeOneSmallSpectrum580.graph DegreeOneSmallSpectrum391.graph
    sourceMap1062 fusedMap1062 sourceMap1062_checked fusedMap1062_checked
    DegreeTwoThreeFiniteComparisons.comparison1062
#print axioms sourceMap1062_checked
#print axioms fusedMap1062_checked
#print axioms certified1062
def sourceMap1062swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,2,3,4,6] (sourceLabel 7 2 0 v)
def fusedMap1062swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (fusedLabel 7 2 0 v)
theorem sourceMap1062swap_checked : acceptsGraphIso
    (source (graph core1062) (root 7) 2 0) DegreeOneSmallSpectrum580.graph sourceMap1062swap=true := by decide +kernel
theorem fusedMap1062swap_checked : acceptsGraphIso
    (fused (graph core1062) (root 7) 2 0) DegreeOneSmallSpectrum391.graph fusedMap1062swap=true := by decide +kernel
theorem certified1062swap : Certified (graph core1062) (root 7) 2 0 :=
  of_native_maps core1062 DegreeOneSmallSpectrum580.graph DegreeOneSmallSpectrum391.graph
    sourceMap1062swap fusedMap1062swap sourceMap1062swap_checked fusedMap1062swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1062
#print axioms sourceMap1062swap_checked
#print axioms fusedMap1062swap_checked
#print axioms certified1062swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
