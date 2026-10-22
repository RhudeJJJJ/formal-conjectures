/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1471 : Family 10 := level10.get ⟨183,by decide⟩
def sourceMap1471 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,10,11,12,13,14,9,6,7,8,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1471 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,6,7,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1471_checked : acceptsGraphIso
    (source (graph core1471) (root 10) 0 2) DegreeTwoThreeSpectrum2848.graph sourceMap1471=true := by decide +kernel
theorem fusedMap1471_checked : acceptsGraphIso
    (fused (graph core1471) (root 10) 0 2) DegreeTwoThreeSpectrum2411.graph fusedMap1471=true := by decide +kernel
theorem certified1471 : Certified (graph core1471) (root 10) 0 2 :=
  of_native_maps core1471 DegreeTwoThreeSpectrum2848.graph DegreeTwoThreeSpectrum2411.graph
    sourceMap1471 fusedMap1471 sourceMap1471_checked fusedMap1471_checked
    DegreeTwoThreeFiniteComparisons.comparison1471
#print axioms sourceMap1471_checked
#print axioms fusedMap1471_checked
#print axioms certified1471
def sourceMap1471swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,10,11,12,13,14,9,6,7,3,4,5,8] (sourceLabel 10 2 0 v)
def fusedMap1471swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,6,7,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1471swap_checked : acceptsGraphIso
    (source (graph core1471) (root 10) 2 0) DegreeTwoThreeSpectrum2848.graph sourceMap1471swap=true := by decide +kernel
theorem fusedMap1471swap_checked : acceptsGraphIso
    (fused (graph core1471) (root 10) 2 0) DegreeTwoThreeSpectrum2411.graph fusedMap1471swap=true := by decide +kernel
theorem certified1471swap : Certified (graph core1471) (root 10) 2 0 :=
  of_native_maps core1471 DegreeTwoThreeSpectrum2848.graph DegreeTwoThreeSpectrum2411.graph
    sourceMap1471swap fusedMap1471swap sourceMap1471swap_checked fusedMap1471swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1471
#print axioms sourceMap1471swap_checked
#print axioms fusedMap1471swap_checked
#print axioms certified1471swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
