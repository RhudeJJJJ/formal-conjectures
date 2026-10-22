/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1644 : Family 10 := level10.get ⟨728,by decide⟩
def sourceMap1644 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1644 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1644_checked : acceptsGraphIso
    (source (graph core1644) (root 10) 0 2) DegreeTwoThreeSpectrum3469.graph sourceMap1644=true := by decide +kernel
theorem fusedMap1644_checked : acceptsGraphIso
    (fused (graph core1644) (root 10) 0 2) DegreeTwoThreeSpectrum2691.graph fusedMap1644=true := by decide +kernel
theorem certified1644 : Certified (graph core1644) (root 10) 0 2 :=
  of_native_maps core1644 DegreeTwoThreeSpectrum3469.graph DegreeTwoThreeSpectrum2691.graph
    sourceMap1644 fusedMap1644 sourceMap1644_checked fusedMap1644_checked
    DegreeTwoThreeFiniteComparisons.comparison1644
#print axioms sourceMap1644_checked
#print axioms fusedMap1644_checked
#print axioms certified1644
def sourceMap1644swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1644swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1644swap_checked : acceptsGraphIso
    (source (graph core1644) (root 10) 2 0) DegreeTwoThreeSpectrum3469.graph sourceMap1644swap=true := by decide +kernel
theorem fusedMap1644swap_checked : acceptsGraphIso
    (fused (graph core1644) (root 10) 2 0) DegreeTwoThreeSpectrum2691.graph fusedMap1644swap=true := by decide +kernel
theorem certified1644swap : Certified (graph core1644) (root 10) 2 0 :=
  of_native_maps core1644 DegreeTwoThreeSpectrum3469.graph DegreeTwoThreeSpectrum2691.graph
    sourceMap1644swap fusedMap1644swap sourceMap1644swap_checked fusedMap1644swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1644
#print axioms sourceMap1644swap_checked
#print axioms fusedMap1644swap_checked
#print axioms certified1644swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
