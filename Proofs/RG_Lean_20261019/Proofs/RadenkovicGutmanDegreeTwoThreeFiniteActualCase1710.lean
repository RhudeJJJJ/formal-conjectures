/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1710 : Family 10 := level10.get ⟨909,by decide⟩
def sourceMap1710 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1710 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1710_checked : acceptsGraphIso
    (source (graph core1710) (root 10) 0 2) DegreeTwoThreeSpectrum3706.graph sourceMap1710=true := by decide +kernel
theorem fusedMap1710_checked : acceptsGraphIso
    (fused (graph core1710) (root 10) 0 2) DegreeTwoThreeSpectrum2922.graph fusedMap1710=true := by decide +kernel
theorem certified1710 : Certified (graph core1710) (root 10) 0 2 :=
  of_native_maps core1710 DegreeTwoThreeSpectrum3706.graph DegreeTwoThreeSpectrum2922.graph
    sourceMap1710 fusedMap1710 sourceMap1710_checked fusedMap1710_checked
    DegreeTwoThreeFiniteComparisons.comparison1710
#print axioms sourceMap1710_checked
#print axioms fusedMap1710_checked
#print axioms certified1710
def sourceMap1710swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1710swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1710swap_checked : acceptsGraphIso
    (source (graph core1710) (root 10) 2 0) DegreeTwoThreeSpectrum3706.graph sourceMap1710swap=true := by decide +kernel
theorem fusedMap1710swap_checked : acceptsGraphIso
    (fused (graph core1710) (root 10) 2 0) DegreeTwoThreeSpectrum2922.graph fusedMap1710swap=true := by decide +kernel
theorem certified1710swap : Certified (graph core1710) (root 10) 2 0 :=
  of_native_maps core1710 DegreeTwoThreeSpectrum3706.graph DegreeTwoThreeSpectrum2922.graph
    sourceMap1710swap fusedMap1710swap sourceMap1710swap_checked fusedMap1710swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1710
#print axioms sourceMap1710swap_checked
#print axioms fusedMap1710swap_checked
#print axioms certified1710swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
