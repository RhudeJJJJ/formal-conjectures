/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1635 : Family 10 := level10.get ⟨704,by decide⟩
def sourceMap1635 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1635 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1635_checked : acceptsGraphIso
    (source (graph core1635) (root 10) 0 2) DegreeTwoThreeSpectrum3433.graph sourceMap1635=true := by decide +kernel
theorem fusedMap1635_checked : acceptsGraphIso
    (fused (graph core1635) (root 10) 0 2) DegreeTwoThreeSpectrum2664.graph fusedMap1635=true := by decide +kernel
theorem certified1635 : Certified (graph core1635) (root 10) 0 2 :=
  of_native_maps core1635 DegreeTwoThreeSpectrum3433.graph DegreeTwoThreeSpectrum2664.graph
    sourceMap1635 fusedMap1635 sourceMap1635_checked fusedMap1635_checked
    DegreeTwoThreeFiniteComparisons.comparison1635
#print axioms sourceMap1635_checked
#print axioms fusedMap1635_checked
#print axioms certified1635
def sourceMap1635swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1635swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1635swap_checked : acceptsGraphIso
    (source (graph core1635) (root 10) 2 0) DegreeTwoThreeSpectrum3433.graph sourceMap1635swap=true := by decide +kernel
theorem fusedMap1635swap_checked : acceptsGraphIso
    (fused (graph core1635) (root 10) 2 0) DegreeTwoThreeSpectrum2664.graph fusedMap1635swap=true := by decide +kernel
theorem certified1635swap : Certified (graph core1635) (root 10) 2 0 :=
  of_native_maps core1635 DegreeTwoThreeSpectrum3433.graph DegreeTwoThreeSpectrum2664.graph
    sourceMap1635swap fusedMap1635swap sourceMap1635swap_checked fusedMap1635swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1635
#print axioms sourceMap1635swap_checked
#print axioms fusedMap1635swap_checked
#print axioms certified1635swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
