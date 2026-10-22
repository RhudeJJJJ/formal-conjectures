/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1363 : Family 9 := level9.get ⟨510,by decide⟩
def sourceMap1363 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1363 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1363_checked : acceptsGraphIso
    (source (graph core1363) (root 9) 0 2) DegreeTwoThreeSpectrum2218.graph sourceMap1363=true := by decide +kernel
theorem fusedMap1363_checked : acceptsGraphIso
    (fused (graph core1363) (root 9) 0 2) DegreeTwoThreeSpectrum2219.graph fusedMap1363=true := by decide +kernel
theorem certified1363 : Certified (graph core1363) (root 9) 0 2 :=
  of_native_maps core1363 DegreeTwoThreeSpectrum2218.graph DegreeTwoThreeSpectrum2219.graph
    sourceMap1363 fusedMap1363 sourceMap1363_checked fusedMap1363_checked
    DegreeTwoThreeFiniteComparisons.comparison1363
#print axioms sourceMap1363_checked
#print axioms fusedMap1363_checked
#print axioms certified1363
def sourceMap1363swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1363swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1363swap_checked : acceptsGraphIso
    (source (graph core1363) (root 9) 2 0) DegreeTwoThreeSpectrum2218.graph sourceMap1363swap=true := by decide +kernel
theorem fusedMap1363swap_checked : acceptsGraphIso
    (fused (graph core1363) (root 9) 2 0) DegreeTwoThreeSpectrum2219.graph fusedMap1363swap=true := by decide +kernel
theorem certified1363swap : Certified (graph core1363) (root 9) 2 0 :=
  of_native_maps core1363 DegreeTwoThreeSpectrum2218.graph DegreeTwoThreeSpectrum2219.graph
    sourceMap1363swap fusedMap1363swap sourceMap1363swap_checked fusedMap1363swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1363
#print axioms sourceMap1363swap_checked
#print axioms fusedMap1363swap_checked
#print axioms certified1363swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
