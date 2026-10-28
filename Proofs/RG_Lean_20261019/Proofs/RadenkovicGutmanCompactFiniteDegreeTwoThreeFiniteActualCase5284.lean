/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5284 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap5284 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,9,6,7,8,0,10,11,12,13,14,15] (sourceLabel 5 2 6 v)
def fusedMap5284 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 2 6 v)
theorem sourceMap5284_checked : acceptsGraphIso
    (source (graph core5284) (root 5) 2 6) DegreeTwoThreeSpectrum4118.graph sourceMap5284=true := by decide +kernel
theorem fusedMap5284_checked : acceptsGraphIso
    (fused (graph core5284) (root 5) 2 6) DegreeTwoThreeSpectrum3882.graph fusedMap5284=true := by decide +kernel
theorem certified5284 : Certified (graph core5284) (root 5) 2 6 :=
  of_native_maps core5284 DegreeTwoThreeSpectrum4118.graph DegreeTwoThreeSpectrum3882.graph
    sourceMap5284 fusedMap5284 sourceMap5284_checked fusedMap5284_checked
    DegreeTwoThreeFiniteComparisons.comparison5284
#print axioms sourceMap5284_checked
#print axioms fusedMap5284_checked
#print axioms certified5284
def sourceMap5284swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,9,0,10,11,12,13,14,15,6,7,8] (sourceLabel 5 6 2 v)
def fusedMap5284swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 6 2 v)
theorem sourceMap5284swap_checked : acceptsGraphIso
    (source (graph core5284) (root 5) 6 2) DegreeTwoThreeSpectrum4118.graph sourceMap5284swap=true := by decide +kernel
theorem fusedMap5284swap_checked : acceptsGraphIso
    (fused (graph core5284) (root 5) 6 2) DegreeTwoThreeSpectrum3882.graph fusedMap5284swap=true := by decide +kernel
theorem certified5284swap : Certified (graph core5284) (root 5) 6 2 :=
  of_native_maps core5284 DegreeTwoThreeSpectrum4118.graph DegreeTwoThreeSpectrum3882.graph
    sourceMap5284swap fusedMap5284swap sourceMap5284swap_checked fusedMap5284swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5284
#print axioms sourceMap5284swap_checked
#print axioms fusedMap5284swap_checked
#print axioms certified5284swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
