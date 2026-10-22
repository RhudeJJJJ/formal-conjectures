/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1042 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap1042 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 5 0 2 v)
def fusedMap1042 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap1042_checked : acceptsGraphIso
    (source (graph core1042) (root 5) 0 2) DegreeOneSmallSpectrum108.graph sourceMap1042=true := by decide +kernel
theorem fusedMap1042_checked : acceptsGraphIso
    (fused (graph core1042) (root 5) 0 2) DegreeOneSmallSpectrum111.graph fusedMap1042=true := by decide +kernel
theorem certified1042 : Certified (graph core1042) (root 5) 0 2 :=
  of_native_maps core1042 DegreeOneSmallSpectrum108.graph DegreeOneSmallSpectrum111.graph
    sourceMap1042 fusedMap1042 sourceMap1042_checked fusedMap1042_checked
    DegreeTwoThreeFiniteComparisons.comparison1042
#print axioms sourceMap1042_checked
#print axioms fusedMap1042_checked
#print axioms certified1042
def sourceMap1042swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,7,8,9,6] (sourceLabel 5 2 0 v)
def fusedMap1042swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap1042swap_checked : acceptsGraphIso
    (source (graph core1042) (root 5) 2 0) DegreeOneSmallSpectrum108.graph sourceMap1042swap=true := by decide +kernel
theorem fusedMap1042swap_checked : acceptsGraphIso
    (fused (graph core1042) (root 5) 2 0) DegreeOneSmallSpectrum111.graph fusedMap1042swap=true := by decide +kernel
theorem certified1042swap : Certified (graph core1042) (root 5) 2 0 :=
  of_native_maps core1042 DegreeOneSmallSpectrum108.graph DegreeOneSmallSpectrum111.graph
    sourceMap1042swap fusedMap1042swap sourceMap1042swap_checked fusedMap1042swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1042
#print axioms sourceMap1042swap_checked
#print axioms fusedMap1042swap_checked
#print axioms certified1042swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
