/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1527 : Family 10 := level10.get ⟨384,by decide⟩
def sourceMap1527 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1527 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1527_checked : acceptsGraphIso
    (source (graph core1527) (root 10) 0 2) DegreeTwoThreeSpectrum2862.graph sourceMap1527=true := by decide +kernel
theorem fusedMap1527_checked : acceptsGraphIso
    (fused (graph core1527) (root 10) 0 2) DegreeTwoThreeSpectrum2864.graph fusedMap1527=true := by decide +kernel
theorem certified1527 : Certified (graph core1527) (root 10) 0 2 :=
  of_native_maps core1527 DegreeTwoThreeSpectrum2862.graph DegreeTwoThreeSpectrum2864.graph
    sourceMap1527 fusedMap1527 sourceMap1527_checked fusedMap1527_checked
    DegreeTwoThreeFiniteComparisons.comparison1527
#print axioms sourceMap1527_checked
#print axioms fusedMap1527_checked
#print axioms certified1527
def sourceMap1527swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1527swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1527swap_checked : acceptsGraphIso
    (source (graph core1527) (root 10) 2 0) DegreeTwoThreeSpectrum2862.graph sourceMap1527swap=true := by decide +kernel
theorem fusedMap1527swap_checked : acceptsGraphIso
    (fused (graph core1527) (root 10) 2 0) DegreeTwoThreeSpectrum2864.graph fusedMap1527swap=true := by decide +kernel
theorem certified1527swap : Certified (graph core1527) (root 10) 2 0 :=
  of_native_maps core1527 DegreeTwoThreeSpectrum2862.graph DegreeTwoThreeSpectrum2864.graph
    sourceMap1527swap fusedMap1527swap sourceMap1527swap_checked fusedMap1527swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1527
#print axioms sourceMap1527swap_checked
#print axioms fusedMap1527swap_checked
#print axioms certified1527swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
