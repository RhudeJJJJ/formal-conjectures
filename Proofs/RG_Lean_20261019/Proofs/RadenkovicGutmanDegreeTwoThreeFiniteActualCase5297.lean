/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5297 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap5297 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,10,11,7,8,9,1,0,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5297 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5297_checked : acceptsGraphIso
    (source (graph core5297) (root 6) 2 6) DegreeTwoThreeSpectrum6349.graph sourceMap5297=true := by decide +kernel
theorem fusedMap5297_checked : acceptsGraphIso
    (fused (graph core5297) (root 6) 2 6) DegreeTwoThreeSpectrum4981.graph fusedMap5297=true := by decide +kernel
theorem certified5297 : Certified (graph core5297) (root 6) 2 6 :=
  of_native_maps core5297 DegreeTwoThreeSpectrum6349.graph DegreeTwoThreeSpectrum4981.graph
    sourceMap5297 fusedMap5297 sourceMap5297_checked fusedMap5297_checked
    DegreeTwoThreeFiniteComparisons.comparison5297
#print axioms sourceMap5297_checked
#print axioms fusedMap5297_checked
#print axioms certified5297
def sourceMap5297swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,3,4,5,6,10,11,1,0,12,13,14,15,16,7,8,9] (sourceLabel 6 6 2 v)
def fusedMap5297swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5297swap_checked : acceptsGraphIso
    (source (graph core5297) (root 6) 6 2) DegreeTwoThreeSpectrum6349.graph sourceMap5297swap=true := by decide +kernel
theorem fusedMap5297swap_checked : acceptsGraphIso
    (fused (graph core5297) (root 6) 6 2) DegreeTwoThreeSpectrum4981.graph fusedMap5297swap=true := by decide +kernel
theorem certified5297swap : Certified (graph core5297) (root 6) 6 2 :=
  of_native_maps core5297 DegreeTwoThreeSpectrum6349.graph DegreeTwoThreeSpectrum4981.graph
    sourceMap5297swap fusedMap5297swap sourceMap5297swap_checked fusedMap5297swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5297
#print axioms sourceMap5297swap_checked
#print axioms fusedMap5297swap_checked
#print axioms certified5297swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
