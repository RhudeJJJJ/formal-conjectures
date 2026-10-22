/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1766 : Family 10 := level10.get ⟨1050,by decide⟩
def sourceMap1766 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1766 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1766_checked : acceptsGraphIso
    (source (graph core1766) (root 10) 0 2) DegreeTwoThreeSpectrum3089.graph sourceMap1766=true := by decide +kernel
theorem fusedMap1766_checked : acceptsGraphIso
    (fused (graph core1766) (root 10) 0 2) DegreeTwoThreeSpectrum3090.graph fusedMap1766=true := by decide +kernel
theorem certified1766 : Certified (graph core1766) (root 10) 0 2 :=
  of_native_maps core1766 DegreeTwoThreeSpectrum3089.graph DegreeTwoThreeSpectrum3090.graph
    sourceMap1766 fusedMap1766 sourceMap1766_checked fusedMap1766_checked
    DegreeTwoThreeFiniteComparisons.comparison1766
#print axioms sourceMap1766_checked
#print axioms fusedMap1766_checked
#print axioms certified1766
def sourceMap1766swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1766swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1766swap_checked : acceptsGraphIso
    (source (graph core1766) (root 10) 2 0) DegreeTwoThreeSpectrum3089.graph sourceMap1766swap=true := by decide +kernel
theorem fusedMap1766swap_checked : acceptsGraphIso
    (fused (graph core1766) (root 10) 2 0) DegreeTwoThreeSpectrum3090.graph fusedMap1766swap=true := by decide +kernel
theorem certified1766swap : Certified (graph core1766) (root 10) 2 0 :=
  of_native_maps core1766 DegreeTwoThreeSpectrum3089.graph DegreeTwoThreeSpectrum3090.graph
    sourceMap1766swap fusedMap1766swap sourceMap1766swap_checked fusedMap1766swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1766
#print axioms sourceMap1766swap_checked
#print axioms fusedMap1766swap_checked
#print axioms certified1766swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
