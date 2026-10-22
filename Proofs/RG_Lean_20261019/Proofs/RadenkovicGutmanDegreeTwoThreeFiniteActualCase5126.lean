/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5126 : Family 8 := level8.get ⟨38,by decide⟩
def sourceMap5126 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5126 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5126_checked : acceptsGraphIso
    (source (graph core5126) (root 8) 2 4) DegreeTwoThreeSpectrum6170.graph sourceMap5126=true := by decide +kernel
theorem fusedMap5126_checked : acceptsGraphIso
    (fused (graph core5126) (root 8) 2 4) DegreeTwoThreeSpectrum4969.graph fusedMap5126=true := by decide +kernel
theorem certified5126 : Certified (graph core5126) (root 8) 2 4 :=
  of_native_maps core5126 DegreeTwoThreeSpectrum6170.graph DegreeTwoThreeSpectrum4969.graph
    sourceMap5126 fusedMap5126 sourceMap5126_checked fusedMap5126_checked
    DegreeTwoThreeFiniteComparisons.comparison5126
#print axioms sourceMap5126_checked
#print axioms fusedMap5126_checked
#print axioms certified5126
def sourceMap5126swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5126swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5126swap_checked : acceptsGraphIso
    (source (graph core5126) (root 8) 4 2) DegreeTwoThreeSpectrum6170.graph sourceMap5126swap=true := by decide +kernel
theorem fusedMap5126swap_checked : acceptsGraphIso
    (fused (graph core5126) (root 8) 4 2) DegreeTwoThreeSpectrum4969.graph fusedMap5126swap=true := by decide +kernel
theorem certified5126swap : Certified (graph core5126) (root 8) 4 2 :=
  of_native_maps core5126 DegreeTwoThreeSpectrum6170.graph DegreeTwoThreeSpectrum4969.graph
    sourceMap5126swap fusedMap5126swap sourceMap5126swap_checked fusedMap5126swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5126
#print axioms sourceMap5126swap_checked
#print axioms fusedMap5126swap_checked
#print axioms certified5126swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
