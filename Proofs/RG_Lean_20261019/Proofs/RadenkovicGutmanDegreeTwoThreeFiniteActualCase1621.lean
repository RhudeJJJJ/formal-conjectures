/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1621 : Family 10 := level10.get ⟨664,by decide⟩
def sourceMap1621 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,10,11,12,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1621 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1621_checked : acceptsGraphIso
    (source (graph core1621) (root 10) 0 2) DegreeTwoThreeSpectrum3363.graph sourceMap1621=true := by decide +kernel
theorem fusedMap1621_checked : acceptsGraphIso
    (fused (graph core1621) (root 10) 0 2) DegreeTwoThreeSpectrum2613.graph fusedMap1621=true := by decide +kernel
theorem certified1621 : Certified (graph core1621) (root 10) 0 2 :=
  of_native_maps core1621 DegreeTwoThreeSpectrum3363.graph DegreeTwoThreeSpectrum2613.graph
    sourceMap1621 fusedMap1621 sourceMap1621_checked fusedMap1621_checked
    DegreeTwoThreeFiniteComparisons.comparison1621
#print axioms sourceMap1621_checked
#print axioms fusedMap1621_checked
#print axioms certified1621
def sourceMap1621swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,10,11,7,8,9,12] (sourceLabel 10 2 0 v)
def fusedMap1621swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1621swap_checked : acceptsGraphIso
    (source (graph core1621) (root 10) 2 0) DegreeTwoThreeSpectrum3363.graph sourceMap1621swap=true := by decide +kernel
theorem fusedMap1621swap_checked : acceptsGraphIso
    (fused (graph core1621) (root 10) 2 0) DegreeTwoThreeSpectrum2613.graph fusedMap1621swap=true := by decide +kernel
theorem certified1621swap : Certified (graph core1621) (root 10) 2 0 :=
  of_native_maps core1621 DegreeTwoThreeSpectrum3363.graph DegreeTwoThreeSpectrum2613.graph
    sourceMap1621swap fusedMap1621swap sourceMap1621swap_checked fusedMap1621swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1621
#print axioms sourceMap1621swap_checked
#print axioms fusedMap1621swap_checked
#print axioms certified1621swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
