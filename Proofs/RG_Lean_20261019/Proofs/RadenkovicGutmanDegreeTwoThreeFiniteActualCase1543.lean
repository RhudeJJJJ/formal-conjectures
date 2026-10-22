/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1543 : Family 10 := level10.get ⟨433,by decide⟩
def sourceMap1543 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1543 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1543_checked : acceptsGraphIso
    (source (graph core1543) (root 10) 0 2) DegreeTwoThreeSpectrum2901.graph sourceMap1543=true := by decide +kernel
theorem fusedMap1543_checked : acceptsGraphIso
    (fused (graph core1543) (root 10) 0 2) DegreeTwoThreeSpectrum2959.graph fusedMap1543=true := by decide +kernel
theorem certified1543 : Certified (graph core1543) (root 10) 0 2 :=
  of_native_maps core1543 DegreeTwoThreeSpectrum2901.graph DegreeTwoThreeSpectrum2959.graph
    sourceMap1543 fusedMap1543 sourceMap1543_checked fusedMap1543_checked
    DegreeTwoThreeFiniteComparisons.comparison1543
#print axioms sourceMap1543_checked
#print axioms fusedMap1543_checked
#print axioms certified1543
def sourceMap1543swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1543swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1543swap_checked : acceptsGraphIso
    (source (graph core1543) (root 10) 2 0) DegreeTwoThreeSpectrum2901.graph sourceMap1543swap=true := by decide +kernel
theorem fusedMap1543swap_checked : acceptsGraphIso
    (fused (graph core1543) (root 10) 2 0) DegreeTwoThreeSpectrum2959.graph fusedMap1543swap=true := by decide +kernel
theorem certified1543swap : Certified (graph core1543) (root 10) 2 0 :=
  of_native_maps core1543 DegreeTwoThreeSpectrum2901.graph DegreeTwoThreeSpectrum2959.graph
    sourceMap1543swap fusedMap1543swap sourceMap1543swap_checked fusedMap1543swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1543
#print axioms sourceMap1543swap_checked
#print axioms fusedMap1543swap_checked
#print axioms certified1543swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
