/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1548 : Family 10 := level10.get ⟨449,by decide⟩
def sourceMap1548 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1548 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1548_checked : acceptsGraphIso
    (source (graph core1548) (root 10) 0 2) DegreeTwoThreeSpectrum2905.graph sourceMap1548=true := by decide +kernel
theorem fusedMap1548_checked : acceptsGraphIso
    (fused (graph core1548) (root 10) 0 2) DegreeTwoThreeSpectrum2984.graph fusedMap1548=true := by decide +kernel
theorem certified1548 : Certified (graph core1548) (root 10) 0 2 :=
  of_native_maps core1548 DegreeTwoThreeSpectrum2905.graph DegreeTwoThreeSpectrum2984.graph
    sourceMap1548 fusedMap1548 sourceMap1548_checked fusedMap1548_checked
    DegreeTwoThreeFiniteComparisons.comparison1548
#print axioms sourceMap1548_checked
#print axioms fusedMap1548_checked
#print axioms certified1548
def sourceMap1548swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1548swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1548swap_checked : acceptsGraphIso
    (source (graph core1548) (root 10) 2 0) DegreeTwoThreeSpectrum2905.graph sourceMap1548swap=true := by decide +kernel
theorem fusedMap1548swap_checked : acceptsGraphIso
    (fused (graph core1548) (root 10) 2 0) DegreeTwoThreeSpectrum2984.graph fusedMap1548swap=true := by decide +kernel
theorem certified1548swap : Certified (graph core1548) (root 10) 2 0 :=
  of_native_maps core1548 DegreeTwoThreeSpectrum2905.graph DegreeTwoThreeSpectrum2984.graph
    sourceMap1548swap fusedMap1548swap sourceMap1548swap_checked fusedMap1548swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1548
#print axioms sourceMap1548swap_checked
#print axioms fusedMap1548swap_checked
#print axioms certified1548swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
