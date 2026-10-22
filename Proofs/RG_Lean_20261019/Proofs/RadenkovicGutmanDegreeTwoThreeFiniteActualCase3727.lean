/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3727 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap3727 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (sourceLabel 3 0 9 v)
def fusedMap3727 : (Vertices 3 ⊕ Fin 11) → Fin 15 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 3 0 9 v)
theorem sourceMap3727_checked : acceptsGraphIso
    (source (graph core3727) (root 3) 0 9) DegreeTwoThreeSpectrum2359.graph sourceMap3727=true := by decide +kernel
theorem fusedMap3727_checked : acceptsGraphIso
    (fused (graph core3727) (root 3) 0 9) DegreeTwoThreeSpectrum2310.graph fusedMap3727=true := by decide +kernel
theorem certified3727 : Certified (graph core3727) (root 3) 0 9 :=
  of_native_maps core3727 DegreeTwoThreeSpectrum2359.graph DegreeTwoThreeSpectrum2310.graph
    sourceMap3727 fusedMap3727 sourceMap3727_checked fusedMap3727_checked
    DegreeTwoThreeFiniteComparisons.comparison3727
#print axioms sourceMap3727_checked
#print axioms fusedMap3727_checked
#print axioms certified3727
def sourceMap3727swap : (Vertices 3 ⊕ Fin 10 ⊕ Fin 1) → Fin 15 :=
  fun v => ![4,5,6,7,3,2,1,0,9,10,11,12,13,14,8] (sourceLabel 3 9 0 v)
def fusedMap3727swap : (Vertices 3 ⊕ Fin 11) → Fin 15 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 3 9 0 v)
theorem sourceMap3727swap_checked : acceptsGraphIso
    (source (graph core3727) (root 3) 9 0) DegreeTwoThreeSpectrum2359.graph sourceMap3727swap=true := by decide +kernel
theorem fusedMap3727swap_checked : acceptsGraphIso
    (fused (graph core3727) (root 3) 9 0) DegreeTwoThreeSpectrum2310.graph fusedMap3727swap=true := by decide +kernel
theorem certified3727swap : Certified (graph core3727) (root 3) 9 0 :=
  of_native_maps core3727 DegreeTwoThreeSpectrum2359.graph DegreeTwoThreeSpectrum2310.graph
    sourceMap3727swap fusedMap3727swap sourceMap3727swap_checked fusedMap3727swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3727
#print axioms sourceMap3727swap_checked
#print axioms fusedMap3727swap_checked
#print axioms certified3727swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
