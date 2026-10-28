/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5152 : Family 8 := level8.get ⟨118,by decide⟩
def sourceMap5152 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5152 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5152_checked : acceptsGraphIso
    (source (graph core5152) (root 8) 2 4) DegreeTwoThreeSpectrum6321.graph sourceMap5152=true := by decide +kernel
theorem fusedMap5152_checked : acceptsGraphIso
    (fused (graph core5152) (root 8) 2 4) DegreeTwoThreeSpectrum5286.graph fusedMap5152=true := by decide +kernel
theorem certified5152 : Certified (graph core5152) (root 8) 2 4 :=
  of_native_maps core5152 DegreeTwoThreeSpectrum6321.graph DegreeTwoThreeSpectrum5286.graph
    sourceMap5152 fusedMap5152 sourceMap5152_checked fusedMap5152_checked
    DegreeTwoThreeFiniteComparisons.comparison5152
#print axioms sourceMap5152_checked
#print axioms fusedMap5152_checked
#print axioms certified5152
def sourceMap5152swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,16,7,8,9] (sourceLabel 8 4 2 v)
def fusedMap5152swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5152swap_checked : acceptsGraphIso
    (source (graph core5152) (root 8) 4 2) DegreeTwoThreeSpectrum6321.graph sourceMap5152swap=true := by decide +kernel
theorem fusedMap5152swap_checked : acceptsGraphIso
    (fused (graph core5152) (root 8) 4 2) DegreeTwoThreeSpectrum5286.graph fusedMap5152swap=true := by decide +kernel
theorem certified5152swap : Certified (graph core5152) (root 8) 4 2 :=
  of_native_maps core5152 DegreeTwoThreeSpectrum6321.graph DegreeTwoThreeSpectrum5286.graph
    sourceMap5152swap fusedMap5152swap sourceMap5152swap_checked fusedMap5152swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5152
#print axioms sourceMap5152swap_checked
#print axioms fusedMap5152swap_checked
#print axioms certified5152swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
