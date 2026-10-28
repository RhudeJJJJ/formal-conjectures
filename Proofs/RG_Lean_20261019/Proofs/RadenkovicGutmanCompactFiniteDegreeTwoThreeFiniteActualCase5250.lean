/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5250 : Family 7 := level7.get ⟨36,by decide⟩
def sourceMap5250 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5250 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5250_checked : acceptsGraphIso
    (source (graph core5250) (root 7) 2 5) DegreeTwoThreeSpectrum6405.graph sourceMap5250=true := by decide +kernel
theorem fusedMap5250_checked : acceptsGraphIso
    (fused (graph core5250) (root 7) 2 5) DegreeTwoThreeSpectrum4983.graph fusedMap5250=true := by decide +kernel
theorem certified5250 : Certified (graph core5250) (root 7) 2 5 :=
  of_native_maps core5250 DegreeTwoThreeSpectrum6405.graph DegreeTwoThreeSpectrum4983.graph
    sourceMap5250 fusedMap5250 sourceMap5250_checked fusedMap5250_checked
    DegreeTwoThreeFiniteComparisons.comparison5250
#print axioms sourceMap5250_checked
#print axioms fusedMap5250_checked
#print axioms certified5250
def sourceMap5250swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,16,8,9,10] (sourceLabel 7 5 2 v)
def fusedMap5250swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5250swap_checked : acceptsGraphIso
    (source (graph core5250) (root 7) 5 2) DegreeTwoThreeSpectrum6405.graph sourceMap5250swap=true := by decide +kernel
theorem fusedMap5250swap_checked : acceptsGraphIso
    (fused (graph core5250) (root 7) 5 2) DegreeTwoThreeSpectrum4983.graph fusedMap5250swap=true := by decide +kernel
theorem certified5250swap : Certified (graph core5250) (root 7) 5 2 :=
  of_native_maps core5250 DegreeTwoThreeSpectrum6405.graph DegreeTwoThreeSpectrum4983.graph
    sourceMap5250swap fusedMap5250swap sourceMap5250swap_checked fusedMap5250swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5250
#print axioms sourceMap5250swap_checked
#print axioms fusedMap5250swap_checked
#print axioms certified5250swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
