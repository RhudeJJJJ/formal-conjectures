/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5188 : Family 8 := level8.get ⟨204,by decide⟩
def sourceMap5188 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,12,7,8,9,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5188 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5188_checked : acceptsGraphIso
    (source (graph core5188) (root 8) 2 4) DegreeTwoThreeSpectrum7151.graph sourceMap5188=true := by decide +kernel
theorem fusedMap5188_checked : acceptsGraphIso
    (fused (graph core5188) (root 8) 2 4) DegreeTwoThreeSpectrum5184.graph fusedMap5188=true := by decide +kernel
theorem certified5188 : Certified (graph core5188) (root 8) 2 4 :=
  of_native_maps core5188 DegreeTwoThreeSpectrum7151.graph DegreeTwoThreeSpectrum5184.graph
    sourceMap5188 fusedMap5188 sourceMap5188_checked fusedMap5188_checked
    DegreeTwoThreeFiniteComparisons.comparison5188
#print axioms sourceMap5188_checked
#print axioms fusedMap5188_checked
#print axioms certified5188
def sourceMap5188swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,12,0,13,14,15,16,7,8,9] (sourceLabel 8 4 2 v)
def fusedMap5188swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5188swap_checked : acceptsGraphIso
    (source (graph core5188) (root 8) 4 2) DegreeTwoThreeSpectrum7151.graph sourceMap5188swap=true := by decide +kernel
theorem fusedMap5188swap_checked : acceptsGraphIso
    (fused (graph core5188) (root 8) 4 2) DegreeTwoThreeSpectrum5184.graph fusedMap5188swap=true := by decide +kernel
theorem certified5188swap : Certified (graph core5188) (root 8) 4 2 :=
  of_native_maps core5188 DegreeTwoThreeSpectrum7151.graph DegreeTwoThreeSpectrum5184.graph
    sourceMap5188swap fusedMap5188swap sourceMap5188swap_checked fusedMap5188swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5188
#print axioms sourceMap5188swap_checked
#print axioms fusedMap5188swap_checked
#print axioms certified5188swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
