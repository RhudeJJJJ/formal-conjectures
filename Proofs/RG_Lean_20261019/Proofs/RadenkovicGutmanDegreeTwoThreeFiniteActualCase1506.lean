/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1506 : Family 10 := level10.get ⟨313,by decide⟩
def sourceMap1506 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1506 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1506_checked : acceptsGraphIso
    (source (graph core1506) (root 10) 0 2) DegreeTwoThreeSpectrum2712.graph sourceMap1506=true := by decide +kernel
theorem fusedMap1506_checked : acceptsGraphIso
    (fused (graph core1506) (root 10) 0 2) DegreeTwoThreeSpectrum2714.graph fusedMap1506=true := by decide +kernel
theorem certified1506 : Certified (graph core1506) (root 10) 0 2 :=
  of_native_maps core1506 DegreeTwoThreeSpectrum2712.graph DegreeTwoThreeSpectrum2714.graph
    sourceMap1506 fusedMap1506 sourceMap1506_checked fusedMap1506_checked
    DegreeTwoThreeFiniteComparisons.comparison1506
#print axioms sourceMap1506_checked
#print axioms fusedMap1506_checked
#print axioms certified1506
def sourceMap1506swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1506swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1506swap_checked : acceptsGraphIso
    (source (graph core1506) (root 10) 2 0) DegreeTwoThreeSpectrum2712.graph sourceMap1506swap=true := by decide +kernel
theorem fusedMap1506swap_checked : acceptsGraphIso
    (fused (graph core1506) (root 10) 2 0) DegreeTwoThreeSpectrum2714.graph fusedMap1506swap=true := by decide +kernel
theorem certified1506swap : Certified (graph core1506) (root 10) 2 0 :=
  of_native_maps core1506 DegreeTwoThreeSpectrum2712.graph DegreeTwoThreeSpectrum2714.graph
    sourceMap1506swap fusedMap1506swap sourceMap1506swap_checked fusedMap1506swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1506
#print axioms sourceMap1506swap_checked
#print axioms fusedMap1506swap_checked
#print axioms certified1506swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
