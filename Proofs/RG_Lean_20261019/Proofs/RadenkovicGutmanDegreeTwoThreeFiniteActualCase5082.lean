/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5082 : Family 7 := level7.get ⟨6,by decide⟩
def sourceMap5082 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,10,11,12,13,14,15,9,6,7,8,1,2,3,4,5] (sourceLabel 7 2 4 v)
def fusedMap5082 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5082_checked : acceptsGraphIso
    (source (graph core5082) (root 7) 2 4) DegreeTwoThreeSpectrum4153.graph sourceMap5082=true := by decide +kernel
theorem fusedMap5082_checked : acceptsGraphIso
    (fused (graph core5082) (root 7) 2 4) DegreeTwoThreeSpectrum3891.graph fusedMap5082=true := by decide +kernel
theorem certified5082 : Certified (graph core5082) (root 7) 2 4 :=
  of_native_maps core5082 DegreeTwoThreeSpectrum4153.graph DegreeTwoThreeSpectrum3891.graph
    sourceMap5082 fusedMap5082 sourceMap5082_checked fusedMap5082_checked
    DegreeTwoThreeFiniteComparisons.comparison5082
#print axioms sourceMap5082_checked
#print axioms fusedMap5082_checked
#print axioms certified5082
def sourceMap5082swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,10,11,12,13,14,15,9,1,2,3,4,5,6,7,8] (sourceLabel 7 4 2 v)
def fusedMap5082swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5082swap_checked : acceptsGraphIso
    (source (graph core5082) (root 7) 4 2) DegreeTwoThreeSpectrum4153.graph sourceMap5082swap=true := by decide +kernel
theorem fusedMap5082swap_checked : acceptsGraphIso
    (fused (graph core5082) (root 7) 4 2) DegreeTwoThreeSpectrum3891.graph fusedMap5082swap=true := by decide +kernel
theorem certified5082swap : Certified (graph core5082) (root 7) 4 2 :=
  of_native_maps core5082 DegreeTwoThreeSpectrum4153.graph DegreeTwoThreeSpectrum3891.graph
    sourceMap5082swap fusedMap5082swap sourceMap5082swap_checked fusedMap5082swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5082
#print axioms sourceMap5082swap_checked
#print axioms fusedMap5082swap_checked
#print axioms certified5082swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
