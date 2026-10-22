/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1059 : Family 7 := level7.get ⟨6,by decide⟩
def sourceMap1059 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 7 0 2 v)
def fusedMap1059 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,6,2,3,4,5] (fusedLabel 7 0 2 v)
theorem sourceMap1059_checked : acceptsGraphIso
    (source (graph core1059) (root 7) 0 2) DegreeOneSmallSpectrum388.graph sourceMap1059=true := by decide +kernel
theorem fusedMap1059_checked : acceptsGraphIso
    (fused (graph core1059) (root 7) 0 2) DegreeOneSmallSpectrum396.graph fusedMap1059=true := by decide +kernel
theorem certified1059 : Certified (graph core1059) (root 7) 0 2 :=
  of_native_maps core1059 DegreeOneSmallSpectrum388.graph DegreeOneSmallSpectrum396.graph
    sourceMap1059 fusedMap1059 sourceMap1059_checked fusedMap1059_checked
    DegreeTwoThreeFiniteComparisons.comparison1059
#print axioms sourceMap1059_checked
#print axioms fusedMap1059_checked
#print axioms certified1059
def sourceMap1059swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,2,3,4,6] (sourceLabel 7 2 0 v)
def fusedMap1059swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,6,2,3,4,5] (fusedLabel 7 2 0 v)
theorem sourceMap1059swap_checked : acceptsGraphIso
    (source (graph core1059) (root 7) 2 0) DegreeOneSmallSpectrum388.graph sourceMap1059swap=true := by decide +kernel
theorem fusedMap1059swap_checked : acceptsGraphIso
    (fused (graph core1059) (root 7) 2 0) DegreeOneSmallSpectrum396.graph fusedMap1059swap=true := by decide +kernel
theorem certified1059swap : Certified (graph core1059) (root 7) 2 0 :=
  of_native_maps core1059 DegreeOneSmallSpectrum388.graph DegreeOneSmallSpectrum396.graph
    sourceMap1059swap fusedMap1059swap sourceMap1059swap_checked fusedMap1059swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1059
#print axioms sourceMap1059swap_checked
#print axioms fusedMap1059swap_checked
#print axioms certified1059swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
