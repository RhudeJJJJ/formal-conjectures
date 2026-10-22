/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1432 : Family 10 := level10.get ⟨17,by decide⟩
def sourceMap1432 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1432 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1432_checked : acceptsGraphIso
    (source (graph core1432) (root 10) 0 2) DegreeTwoThreeSpectrum2343.graph sourceMap1432=true := by decide +kernel
theorem fusedMap1432_checked : acceptsGraphIso
    (fused (graph core1432) (root 10) 0 2) DegreeTwoThreeSpectrum2346.graph fusedMap1432=true := by decide +kernel
theorem certified1432 : Certified (graph core1432) (root 10) 0 2 :=
  of_native_maps core1432 DegreeTwoThreeSpectrum2343.graph DegreeTwoThreeSpectrum2346.graph
    sourceMap1432 fusedMap1432 sourceMap1432_checked fusedMap1432_checked
    DegreeTwoThreeFiniteComparisons.comparison1432
#print axioms sourceMap1432_checked
#print axioms fusedMap1432_checked
#print axioms certified1432
def sourceMap1432swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1432swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1432swap_checked : acceptsGraphIso
    (source (graph core1432) (root 10) 2 0) DegreeTwoThreeSpectrum2343.graph sourceMap1432swap=true := by decide +kernel
theorem fusedMap1432swap_checked : acceptsGraphIso
    (fused (graph core1432) (root 10) 2 0) DegreeTwoThreeSpectrum2346.graph fusedMap1432swap=true := by decide +kernel
theorem certified1432swap : Certified (graph core1432) (root 10) 2 0 :=
  of_native_maps core1432 DegreeTwoThreeSpectrum2343.graph DegreeTwoThreeSpectrum2346.graph
    sourceMap1432swap fusedMap1432swap sourceMap1432swap_checked fusedMap1432swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1432
#print axioms sourceMap1432swap_checked
#print axioms fusedMap1432swap_checked
#print axioms certified1432swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
