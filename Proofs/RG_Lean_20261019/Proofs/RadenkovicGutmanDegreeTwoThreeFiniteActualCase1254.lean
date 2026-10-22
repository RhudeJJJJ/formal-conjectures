/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1254 : Family 9 := level9.get ⟨233,by decide⟩
def sourceMap1254 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1254 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1254_checked : acceptsGraphIso
    (source (graph core1254) (root 9) 0 2) DegreeTwoThreeSpectrum2159.graph sourceMap1254=true := by decide +kernel
theorem fusedMap1254_checked : acceptsGraphIso
    (fused (graph core1254) (root 9) 0 2) DegreeTwoThreeSpectrum1835.graph fusedMap1254=true := by decide +kernel
theorem certified1254 : Certified (graph core1254) (root 9) 0 2 :=
  of_native_maps core1254 DegreeTwoThreeSpectrum2159.graph DegreeTwoThreeSpectrum1835.graph
    sourceMap1254 fusedMap1254 sourceMap1254_checked fusedMap1254_checked
    DegreeTwoThreeFiniteComparisons.comparison1254
#print axioms sourceMap1254_checked
#print axioms fusedMap1254_checked
#print axioms certified1254
def sourceMap1254swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1254swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1254swap_checked : acceptsGraphIso
    (source (graph core1254) (root 9) 2 0) DegreeTwoThreeSpectrum2159.graph sourceMap1254swap=true := by decide +kernel
theorem fusedMap1254swap_checked : acceptsGraphIso
    (fused (graph core1254) (root 9) 2 0) DegreeTwoThreeSpectrum1835.graph fusedMap1254swap=true := by decide +kernel
theorem certified1254swap : Certified (graph core1254) (root 9) 2 0 :=
  of_native_maps core1254 DegreeTwoThreeSpectrum2159.graph DegreeTwoThreeSpectrum1835.graph
    sourceMap1254swap fusedMap1254swap sourceMap1254swap_checked fusedMap1254swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1254
#print axioms sourceMap1254swap_checked
#print axioms fusedMap1254swap_checked
#print axioms certified1254swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
