/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1390 : Family 9 := level9.get ⟨574,by decide⟩
def sourceMap1390 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1390 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1390_checked : acceptsGraphIso
    (source (graph core1390) (root 9) 0 2) DegreeTwoThreeSpectrum2261.graph sourceMap1390=true := by decide +kernel
theorem fusedMap1390_checked : acceptsGraphIso
    (fused (graph core1390) (root 9) 0 2) DegreeTwoThreeSpectrum1962.graph fusedMap1390=true := by decide +kernel
theorem certified1390 : Certified (graph core1390) (root 9) 0 2 :=
  of_native_maps core1390 DegreeTwoThreeSpectrum2261.graph DegreeTwoThreeSpectrum1962.graph
    sourceMap1390 fusedMap1390 sourceMap1390_checked fusedMap1390_checked
    DegreeTwoThreeFiniteComparisons.comparison1390
#print axioms sourceMap1390_checked
#print axioms fusedMap1390_checked
#print axioms certified1390
def sourceMap1390swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,7,8,9,13] (sourceLabel 9 2 0 v)
def fusedMap1390swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1390swap_checked : acceptsGraphIso
    (source (graph core1390) (root 9) 2 0) DegreeTwoThreeSpectrum2261.graph sourceMap1390swap=true := by decide +kernel
theorem fusedMap1390swap_checked : acceptsGraphIso
    (fused (graph core1390) (root 9) 2 0) DegreeTwoThreeSpectrum1962.graph fusedMap1390swap=true := by decide +kernel
theorem certified1390swap : Certified (graph core1390) (root 9) 2 0 :=
  of_native_maps core1390 DegreeTwoThreeSpectrum2261.graph DegreeTwoThreeSpectrum1962.graph
    sourceMap1390swap fusedMap1390swap sourceMap1390swap_checked fusedMap1390swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1390
#print axioms sourceMap1390swap_checked
#print axioms fusedMap1390swap_checked
#print axioms certified1390swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
