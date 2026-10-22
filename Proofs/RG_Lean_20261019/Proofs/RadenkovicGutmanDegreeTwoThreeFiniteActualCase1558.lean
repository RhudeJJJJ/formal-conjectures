/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1558 : Family 10 := level10.get ⟨477,by decide⟩
def sourceMap1558 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,7,8,9,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1558 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1558_checked : acceptsGraphIso
    (source (graph core1558) (root 10) 0 2) DegreeTwoThreeSpectrum2881.graph sourceMap1558=true := by decide +kernel
theorem fusedMap1558_checked : acceptsGraphIso
    (fused (graph core1558) (root 10) 0 2) DegreeTwoThreeSpectrum2991.graph fusedMap1558=true := by decide +kernel
theorem certified1558 : Certified (graph core1558) (root 10) 0 2 :=
  of_native_maps core1558 DegreeTwoThreeSpectrum2881.graph DegreeTwoThreeSpectrum2991.graph
    sourceMap1558 fusedMap1558 sourceMap1558_checked fusedMap1558_checked
    DegreeTwoThreeFiniteComparisons.comparison1558
#print axioms sourceMap1558_checked
#print axioms fusedMap1558_checked
#print axioms certified1558
def sourceMap1558swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,7,8,9,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1558swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1558swap_checked : acceptsGraphIso
    (source (graph core1558) (root 10) 2 0) DegreeTwoThreeSpectrum2881.graph sourceMap1558swap=true := by decide +kernel
theorem fusedMap1558swap_checked : acceptsGraphIso
    (fused (graph core1558) (root 10) 2 0) DegreeTwoThreeSpectrum2991.graph fusedMap1558swap=true := by decide +kernel
theorem certified1558swap : Certified (graph core1558) (root 10) 2 0 :=
  of_native_maps core1558 DegreeTwoThreeSpectrum2881.graph DegreeTwoThreeSpectrum2991.graph
    sourceMap1558swap fusedMap1558swap sourceMap1558swap_checked fusedMap1558swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1558
#print axioms sourceMap1558swap_checked
#print axioms fusedMap1558swap_checked
#print axioms certified1558swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
