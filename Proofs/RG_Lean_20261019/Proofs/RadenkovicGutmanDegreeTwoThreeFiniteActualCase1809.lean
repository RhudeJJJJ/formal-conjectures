/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1809 : Family 10 := level10.get ⟨1159,by decide⟩
def sourceMap1809 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1809 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1809_checked : acceptsGraphIso
    (source (graph core1809) (root 10) 0 2) DegreeTwoThreeSpectrum3254.graph sourceMap1809=true := by decide +kernel
theorem fusedMap1809_checked : acceptsGraphIso
    (fused (graph core1809) (root 10) 0 2) DegreeTwoThreeSpectrum3255.graph fusedMap1809=true := by decide +kernel
theorem certified1809 : Certified (graph core1809) (root 10) 0 2 :=
  of_native_maps core1809 DegreeTwoThreeSpectrum3254.graph DegreeTwoThreeSpectrum3255.graph
    sourceMap1809 fusedMap1809 sourceMap1809_checked fusedMap1809_checked
    DegreeTwoThreeFiniteComparisons.comparison1809
#print axioms sourceMap1809_checked
#print axioms fusedMap1809_checked
#print axioms certified1809
def sourceMap1809swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1809swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1809swap_checked : acceptsGraphIso
    (source (graph core1809) (root 10) 2 0) DegreeTwoThreeSpectrum3254.graph sourceMap1809swap=true := by decide +kernel
theorem fusedMap1809swap_checked : acceptsGraphIso
    (fused (graph core1809) (root 10) 2 0) DegreeTwoThreeSpectrum3255.graph fusedMap1809swap=true := by decide +kernel
theorem certified1809swap : Certified (graph core1809) (root 10) 2 0 :=
  of_native_maps core1809 DegreeTwoThreeSpectrum3254.graph DegreeTwoThreeSpectrum3255.graph
    sourceMap1809swap fusedMap1809swap sourceMap1809swap_checked fusedMap1809swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1809
#print axioms sourceMap1809swap_checked
#print axioms fusedMap1809swap_checked
#print axioms certified1809swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
