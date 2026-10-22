/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5248 : Family 7 := level7.get ⟨29,by decide⟩
def sourceMap5248 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5248 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5248_checked : acceptsGraphIso
    (source (graph core5248) (root 7) 2 5) DegreeTwoThreeSpectrum6159.graph sourceMap5248=true := by decide +kernel
theorem fusedMap5248_checked : acceptsGraphIso
    (fused (graph core5248) (root 7) 2 5) DegreeTwoThreeSpectrum4968.graph fusedMap5248=true := by decide +kernel
theorem certified5248 : Certified (graph core5248) (root 7) 2 5 :=
  of_native_maps core5248 DegreeTwoThreeSpectrum6159.graph DegreeTwoThreeSpectrum4968.graph
    sourceMap5248 fusedMap5248 sourceMap5248_checked fusedMap5248_checked
    DegreeTwoThreeFiniteComparisons.comparison5248
#print axioms sourceMap5248_checked
#print axioms fusedMap5248_checked
#print axioms certified5248
def sourceMap5248swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,16,8,9,10] (sourceLabel 7 5 2 v)
def fusedMap5248swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5248swap_checked : acceptsGraphIso
    (source (graph core5248) (root 7) 5 2) DegreeTwoThreeSpectrum6159.graph sourceMap5248swap=true := by decide +kernel
theorem fusedMap5248swap_checked : acceptsGraphIso
    (fused (graph core5248) (root 7) 5 2) DegreeTwoThreeSpectrum4968.graph fusedMap5248swap=true := by decide +kernel
theorem certified5248swap : Certified (graph core5248) (root 7) 5 2 :=
  of_native_maps core5248 DegreeTwoThreeSpectrum6159.graph DegreeTwoThreeSpectrum4968.graph
    sourceMap5248swap fusedMap5248swap sourceMap5248swap_checked fusedMap5248swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5248
#print axioms sourceMap5248swap_checked
#print axioms fusedMap5248swap_checked
#print axioms certified5248swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
