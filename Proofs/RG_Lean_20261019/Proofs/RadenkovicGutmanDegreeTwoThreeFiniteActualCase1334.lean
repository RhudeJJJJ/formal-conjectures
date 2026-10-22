/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1334 : Family 9 := level9.get ⟨443,by decide⟩
def sourceMap1334 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1334 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1334_checked : acceptsGraphIso
    (source (graph core1334) (root 9) 0 2) DegreeTwoThreeSpectrum2119.graph sourceMap1334=true := by decide +kernel
theorem fusedMap1334_checked : acceptsGraphIso
    (fused (graph core1334) (root 9) 0 2) DegreeTwoThreeSpectrum2120.graph fusedMap1334=true := by decide +kernel
theorem certified1334 : Certified (graph core1334) (root 9) 0 2 :=
  of_native_maps core1334 DegreeTwoThreeSpectrum2119.graph DegreeTwoThreeSpectrum2120.graph
    sourceMap1334 fusedMap1334 sourceMap1334_checked fusedMap1334_checked
    DegreeTwoThreeFiniteComparisons.comparison1334
#print axioms sourceMap1334_checked
#print axioms fusedMap1334_checked
#print axioms certified1334
def sourceMap1334swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1334swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1334swap_checked : acceptsGraphIso
    (source (graph core1334) (root 9) 2 0) DegreeTwoThreeSpectrum2119.graph sourceMap1334swap=true := by decide +kernel
theorem fusedMap1334swap_checked : acceptsGraphIso
    (fused (graph core1334) (root 9) 2 0) DegreeTwoThreeSpectrum2120.graph fusedMap1334swap=true := by decide +kernel
theorem certified1334swap : Certified (graph core1334) (root 9) 2 0 :=
  of_native_maps core1334 DegreeTwoThreeSpectrum2119.graph DegreeTwoThreeSpectrum2120.graph
    sourceMap1334swap fusedMap1334swap sourceMap1334swap_checked fusedMap1334swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1334
#print axioms sourceMap1334swap_checked
#print axioms fusedMap1334swap_checked
#print axioms certified1334swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
