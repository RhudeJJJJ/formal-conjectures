/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1735 : Family 10 := level10.get ⟨966,by decide⟩
def sourceMap1735 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1735 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,5,6,7,8] (fusedLabel 10 0 2 v)
theorem sourceMap1735_checked : acceptsGraphIso
    (source (graph core1735) (root 10) 0 2) DegreeTwoThreeSpectrum2955.graph sourceMap1735=true := by decide +kernel
theorem fusedMap1735_checked : acceptsGraphIso
    (fused (graph core1735) (root 10) 0 2) DegreeTwoThreeSpectrum2942.graph fusedMap1735=true := by decide +kernel
theorem certified1735 : Certified (graph core1735) (root 10) 0 2 :=
  of_native_maps core1735 DegreeTwoThreeSpectrum2955.graph DegreeTwoThreeSpectrum2942.graph
    sourceMap1735 fusedMap1735 sourceMap1735_checked fusedMap1735_checked
    DegreeTwoThreeFiniteComparisons.comparison1735
#print axioms sourceMap1735_checked
#print axioms fusedMap1735_checked
#print axioms certified1735
def sourceMap1735swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1735swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,5,6,7,8] (fusedLabel 10 2 0 v)
theorem sourceMap1735swap_checked : acceptsGraphIso
    (source (graph core1735) (root 10) 2 0) DegreeTwoThreeSpectrum2955.graph sourceMap1735swap=true := by decide +kernel
theorem fusedMap1735swap_checked : acceptsGraphIso
    (fused (graph core1735) (root 10) 2 0) DegreeTwoThreeSpectrum2942.graph fusedMap1735swap=true := by decide +kernel
theorem certified1735swap : Certified (graph core1735) (root 10) 2 0 :=
  of_native_maps core1735 DegreeTwoThreeSpectrum2955.graph DegreeTwoThreeSpectrum2942.graph
    sourceMap1735swap fusedMap1735swap sourceMap1735swap_checked fusedMap1735swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1735
#print axioms sourceMap1735swap_checked
#print axioms fusedMap1735swap_checked
#print axioms certified1735swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
