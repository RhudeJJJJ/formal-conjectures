/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1511 : Family 10 := level10.get ⟨332,by decide⟩
def sourceMap1511 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1511 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1511_checked : acceptsGraphIso
    (source (graph core1511) (root 10) 0 2) DegreeTwoThreeSpectrum2752.graph sourceMap1511=true := by decide +kernel
theorem fusedMap1511_checked : acceptsGraphIso
    (fused (graph core1511) (root 10) 0 2) DegreeTwoThreeSpectrum2754.graph fusedMap1511=true := by decide +kernel
theorem certified1511 : Certified (graph core1511) (root 10) 0 2 :=
  of_native_maps core1511 DegreeTwoThreeSpectrum2752.graph DegreeTwoThreeSpectrum2754.graph
    sourceMap1511 fusedMap1511 sourceMap1511_checked fusedMap1511_checked
    DegreeTwoThreeFiniteComparisons.comparison1511
#print axioms sourceMap1511_checked
#print axioms fusedMap1511_checked
#print axioms certified1511
def sourceMap1511swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1511swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1511swap_checked : acceptsGraphIso
    (source (graph core1511) (root 10) 2 0) DegreeTwoThreeSpectrum2752.graph sourceMap1511swap=true := by decide +kernel
theorem fusedMap1511swap_checked : acceptsGraphIso
    (fused (graph core1511) (root 10) 2 0) DegreeTwoThreeSpectrum2754.graph fusedMap1511swap=true := by decide +kernel
theorem certified1511swap : Certified (graph core1511) (root 10) 2 0 :=
  of_native_maps core1511 DegreeTwoThreeSpectrum2752.graph DegreeTwoThreeSpectrum2754.graph
    sourceMap1511swap fusedMap1511swap sourceMap1511swap_checked fusedMap1511swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1511
#print axioms sourceMap1511swap_checked
#print axioms fusedMap1511swap_checked
#print axioms certified1511swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
