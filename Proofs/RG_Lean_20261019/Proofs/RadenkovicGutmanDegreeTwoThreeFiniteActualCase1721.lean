/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1721 : Family 10 := level10.get ⟨937,by decide⟩
def sourceMap1721 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1721 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1721_checked : acceptsGraphIso
    (source (graph core1721) (root 10) 0 2) DegreeTwoThreeSpectrum3710.graph sourceMap1721=true := by decide +kernel
theorem fusedMap1721_checked : acceptsGraphIso
    (fused (graph core1721) (root 10) 0 2) DegreeTwoThreeSpectrum2955.graph fusedMap1721=true := by decide +kernel
theorem certified1721 : Certified (graph core1721) (root 10) 0 2 :=
  of_native_maps core1721 DegreeTwoThreeSpectrum3710.graph DegreeTwoThreeSpectrum2955.graph
    sourceMap1721 fusedMap1721 sourceMap1721_checked fusedMap1721_checked
    DegreeTwoThreeFiniteComparisons.comparison1721
#print axioms sourceMap1721_checked
#print axioms fusedMap1721_checked
#print axioms certified1721
def sourceMap1721swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1721swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1721swap_checked : acceptsGraphIso
    (source (graph core1721) (root 10) 2 0) DegreeTwoThreeSpectrum3710.graph sourceMap1721swap=true := by decide +kernel
theorem fusedMap1721swap_checked : acceptsGraphIso
    (fused (graph core1721) (root 10) 2 0) DegreeTwoThreeSpectrum2955.graph fusedMap1721swap=true := by decide +kernel
theorem certified1721swap : Certified (graph core1721) (root 10) 2 0 :=
  of_native_maps core1721 DegreeTwoThreeSpectrum3710.graph DegreeTwoThreeSpectrum2955.graph
    sourceMap1721swap fusedMap1721swap sourceMap1721swap_checked fusedMap1721swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1721
#print axioms sourceMap1721swap_checked
#print axioms fusedMap1721swap_checked
#print axioms certified1721swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
