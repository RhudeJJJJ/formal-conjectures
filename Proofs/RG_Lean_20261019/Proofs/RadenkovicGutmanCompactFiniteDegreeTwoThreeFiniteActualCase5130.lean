/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5130 : Family 8 := level8.get ⟨51,by decide⟩
def sourceMap5130 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,15,16,12,13,14,7,8,9,10,11] (sourceLabel 8 2 4 v)
def fusedMap5130 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5130_checked : acceptsGraphIso
    (source (graph core5130) (root 8) 2 4) DegreeTwoThreeSpectrum6466.graph sourceMap5130=true := by decide +kernel
theorem fusedMap5130_checked : acceptsGraphIso
    (fused (graph core5130) (root 8) 2 4) DegreeTwoThreeSpectrum4994.graph fusedMap5130=true := by decide +kernel
theorem certified5130 : Certified (graph core5130) (root 8) 2 4 :=
  of_native_maps core5130 DegreeTwoThreeSpectrum6466.graph DegreeTwoThreeSpectrum4994.graph
    sourceMap5130 fusedMap5130 sourceMap5130_checked fusedMap5130_checked
    DegreeTwoThreeFiniteComparisons.comparison5130
#print axioms sourceMap5130_checked
#print axioms fusedMap5130_checked
#print axioms certified5130
def sourceMap5130swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,15,16,7,8,9,10,11,12,13,14] (sourceLabel 8 4 2 v)
def fusedMap5130swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5130swap_checked : acceptsGraphIso
    (source (graph core5130) (root 8) 4 2) DegreeTwoThreeSpectrum6466.graph sourceMap5130swap=true := by decide +kernel
theorem fusedMap5130swap_checked : acceptsGraphIso
    (fused (graph core5130) (root 8) 4 2) DegreeTwoThreeSpectrum4994.graph fusedMap5130swap=true := by decide +kernel
theorem certified5130swap : Certified (graph core5130) (root 8) 4 2 :=
  of_native_maps core5130 DegreeTwoThreeSpectrum6466.graph DegreeTwoThreeSpectrum4994.graph
    sourceMap5130swap fusedMap5130swap sourceMap5130swap_checked fusedMap5130swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5130
#print axioms sourceMap5130swap_checked
#print axioms fusedMap5130swap_checked
#print axioms certified5130swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
