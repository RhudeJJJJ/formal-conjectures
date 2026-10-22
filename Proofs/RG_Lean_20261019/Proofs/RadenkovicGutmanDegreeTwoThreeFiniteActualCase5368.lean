/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5368 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5368 : (Vertices 2 ⊕ Fin 4 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,7,8,3,4,5,6,1,0,9,10,11,12,13,14] (sourceLabel 2 3 7 v)
def fusedMap5368 : (Vertices 2 ⊕ Fin 12) → Fin 15 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 2 3 7 v)
theorem sourceMap5368_checked : acceptsGraphIso
    (source (graph core5368) (root 2) 3 7) DegreeTwoThreeSpectrum2417.graph sourceMap5368=true := by decide +kernel
theorem fusedMap5368_checked : acceptsGraphIso
    (fused (graph core5368) (root 2) 3 7) DegreeTwoThreeSpectrum2309.graph fusedMap5368=true := by decide +kernel
theorem certified5368 : Certified (graph core5368) (root 2) 3 7 :=
  of_native_maps core5368 DegreeTwoThreeSpectrum2417.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap5368 fusedMap5368 sourceMap5368_checked fusedMap5368_checked
    DegreeTwoThreeFiniteComparisons.comparison5368
#print axioms sourceMap5368_checked
#print axioms fusedMap5368_checked
#print axioms certified5368
def sourceMap5368swap : (Vertices 2 ⊕ Fin 8 ⊕ Fin 4) → Fin 15 :=
  fun v => ![2,7,8,1,0,9,10,11,12,13,14,3,4,5,6] (sourceLabel 2 7 3 v)
def fusedMap5368swap : (Vertices 2 ⊕ Fin 12) → Fin 15 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 2 7 3 v)
theorem sourceMap5368swap_checked : acceptsGraphIso
    (source (graph core5368) (root 2) 7 3) DegreeTwoThreeSpectrum2417.graph sourceMap5368swap=true := by decide +kernel
theorem fusedMap5368swap_checked : acceptsGraphIso
    (fused (graph core5368) (root 2) 7 3) DegreeTwoThreeSpectrum2309.graph fusedMap5368swap=true := by decide +kernel
theorem certified5368swap : Certified (graph core5368) (root 2) 7 3 :=
  of_native_maps core5368 DegreeTwoThreeSpectrum2417.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap5368swap fusedMap5368swap sourceMap5368swap_checked fusedMap5368swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5368
#print axioms sourceMap5368swap_checked
#print axioms fusedMap5368swap_checked
#print axioms certified5368swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
