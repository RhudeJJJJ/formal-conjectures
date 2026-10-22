/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1074 : Family 7 := level7.get ⟨55,by decide⟩
def sourceMap1074 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,4,5,1,2,3] (sourceLabel 7 0 2 v)
def fusedMap1074 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 0 2 v)
theorem sourceMap1074_checked : acceptsGraphIso
    (source (graph core1074) (root 7) 0 2) DegreeOneSmallSpectrum579.graph sourceMap1074=true := by decide +kernel
theorem fusedMap1074_checked : acceptsGraphIso
    (fused (graph core1074) (root 7) 0 2) DegreeOneSmallSpectrum581.graph fusedMap1074=true := by decide +kernel
theorem certified1074 : Certified (graph core1074) (root 7) 0 2 :=
  of_native_maps core1074 DegreeOneSmallSpectrum579.graph DegreeOneSmallSpectrum581.graph
    sourceMap1074 fusedMap1074 sourceMap1074_checked fusedMap1074_checked
    DegreeTwoThreeFiniteComparisons.comparison1074
#print axioms sourceMap1074_checked
#print axioms fusedMap1074_checked
#print axioms certified1074
def sourceMap1074swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,4,1,2,3,5] (sourceLabel 7 2 0 v)
def fusedMap1074swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (fusedLabel 7 2 0 v)
theorem sourceMap1074swap_checked : acceptsGraphIso
    (source (graph core1074) (root 7) 2 0) DegreeOneSmallSpectrum579.graph sourceMap1074swap=true := by decide +kernel
theorem fusedMap1074swap_checked : acceptsGraphIso
    (fused (graph core1074) (root 7) 2 0) DegreeOneSmallSpectrum581.graph fusedMap1074swap=true := by decide +kernel
theorem certified1074swap : Certified (graph core1074) (root 7) 2 0 :=
  of_native_maps core1074 DegreeOneSmallSpectrum579.graph DegreeOneSmallSpectrum581.graph
    sourceMap1074swap fusedMap1074swap sourceMap1074swap_checked fusedMap1074swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1074
#print axioms sourceMap1074swap_checked
#print axioms fusedMap1074swap_checked
#print axioms certified1074swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
