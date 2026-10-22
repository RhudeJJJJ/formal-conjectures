/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1372 : Family 9 := level9.get ⟨528,by decide⟩
def sourceMap1372 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,10,11,12,13,1,2,3,4,5,9,6,7,8] (sourceLabel 9 0 2 v)
def fusedMap1372 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,5,6,7,8] (fusedLabel 9 0 2 v)
theorem sourceMap1372_checked : acceptsGraphIso
    (source (graph core1372) (root 9) 0 2) DegreeTwoThreeSpectrum2021.graph sourceMap1372=true := by decide +kernel
theorem fusedMap1372_checked : acceptsGraphIso
    (fused (graph core1372) (root 9) 0 2) DegreeTwoThreeSpectrum2235.graph fusedMap1372=true := by decide +kernel
theorem certified1372 : Certified (graph core1372) (root 9) 0 2 :=
  of_native_maps core1372 DegreeTwoThreeSpectrum2021.graph DegreeTwoThreeSpectrum2235.graph
    sourceMap1372 fusedMap1372 sourceMap1372_checked fusedMap1372_checked
    DegreeTwoThreeFiniteComparisons.comparison1372
#print axioms sourceMap1372_checked
#print axioms fusedMap1372_checked
#print axioms certified1372
def sourceMap1372swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,10,11,12,13,1,2,3,4,5,6,7,8,9] (sourceLabel 9 2 0 v)
def fusedMap1372swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,5,6,7,8] (fusedLabel 9 2 0 v)
theorem sourceMap1372swap_checked : acceptsGraphIso
    (source (graph core1372) (root 9) 2 0) DegreeTwoThreeSpectrum2021.graph sourceMap1372swap=true := by decide +kernel
theorem fusedMap1372swap_checked : acceptsGraphIso
    (fused (graph core1372) (root 9) 2 0) DegreeTwoThreeSpectrum2235.graph fusedMap1372swap=true := by decide +kernel
theorem certified1372swap : Certified (graph core1372) (root 9) 2 0 :=
  of_native_maps core1372 DegreeTwoThreeSpectrum2021.graph DegreeTwoThreeSpectrum2235.graph
    sourceMap1372swap fusedMap1372swap sourceMap1372swap_checked fusedMap1372swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1372
#print axioms sourceMap1372swap_checked
#print axioms fusedMap1372swap_checked
#print axioms certified1372swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
