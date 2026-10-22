/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3640 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap3640 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (sourceLabel 5 0 7 v)
def fusedMap3640 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13,14] (fusedLabel 5 0 7 v)
theorem sourceMap3640_checked : acceptsGraphIso
    (source (graph core3640) (root 5) 0 7) DegreeTwoThreeSpectrum2417.graph sourceMap3640=true := by decide +kernel
theorem fusedMap3640_checked : acceptsGraphIso
    (fused (graph core3640) (root 5) 0 7) DegreeTwoThreeSpectrum2312.graph fusedMap3640=true := by decide +kernel
theorem certified3640 : Certified (graph core3640) (root 5) 0 7 :=
  of_native_maps core3640 DegreeTwoThreeSpectrum2417.graph DegreeTwoThreeSpectrum2312.graph
    sourceMap3640 fusedMap3640 sourceMap3640_checked fusedMap3640_checked
    DegreeTwoThreeFiniteComparisons.comparison3640
#print axioms sourceMap3640_checked
#print axioms fusedMap3640_checked
#print axioms certified3640
def sourceMap3640swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,13,14,8] (sourceLabel 5 7 0 v)
def fusedMap3640swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13,14] (fusedLabel 5 7 0 v)
theorem sourceMap3640swap_checked : acceptsGraphIso
    (source (graph core3640) (root 5) 7 0) DegreeTwoThreeSpectrum2417.graph sourceMap3640swap=true := by decide +kernel
theorem fusedMap3640swap_checked : acceptsGraphIso
    (fused (graph core3640) (root 5) 7 0) DegreeTwoThreeSpectrum2312.graph fusedMap3640swap=true := by decide +kernel
theorem certified3640swap : Certified (graph core3640) (root 5) 7 0 :=
  of_native_maps core3640 DegreeTwoThreeSpectrum2417.graph DegreeTwoThreeSpectrum2312.graph
    sourceMap3640swap fusedMap3640swap sourceMap3640swap_checked fusedMap3640swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3640
#print axioms sourceMap3640swap_checked
#print axioms fusedMap3640swap_checked
#print axioms certified3640swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
