/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1386 : Family 9 := level9.get ⟨567,by decide⟩
def sourceMap1386 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1386 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1386_checked : acceptsGraphIso
    (source (graph core1386) (root 9) 0 2) DegreeTwoThreeSpectrum2257.graph sourceMap1386=true := by decide +kernel
theorem fusedMap1386_checked : acceptsGraphIso
    (fused (graph core1386) (root 9) 0 2) DegreeTwoThreeSpectrum1954.graph fusedMap1386=true := by decide +kernel
theorem certified1386 : Certified (graph core1386) (root 9) 0 2 :=
  of_native_maps core1386 DegreeTwoThreeSpectrum2257.graph DegreeTwoThreeSpectrum1954.graph
    sourceMap1386 fusedMap1386 sourceMap1386_checked fusedMap1386_checked
    DegreeTwoThreeFiniteComparisons.comparison1386
#print axioms sourceMap1386_checked
#print axioms fusedMap1386_checked
#print axioms certified1386
def sourceMap1386swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1386swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1386swap_checked : acceptsGraphIso
    (source (graph core1386) (root 9) 2 0) DegreeTwoThreeSpectrum2257.graph sourceMap1386swap=true := by decide +kernel
theorem fusedMap1386swap_checked : acceptsGraphIso
    (fused (graph core1386) (root 9) 2 0) DegreeTwoThreeSpectrum1954.graph fusedMap1386swap=true := by decide +kernel
theorem certified1386swap : Certified (graph core1386) (root 9) 2 0 :=
  of_native_maps core1386 DegreeTwoThreeSpectrum2257.graph DegreeTwoThreeSpectrum1954.graph
    sourceMap1386swap fusedMap1386swap sourceMap1386swap_checked fusedMap1386swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1386
#print axioms sourceMap1386swap_checked
#print axioms fusedMap1386swap_checked
#print axioms certified1386swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
