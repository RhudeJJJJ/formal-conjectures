/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5118 : Family 7 := level7.get ⟨104,by decide⟩
def sourceMap5118 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,5,6,7,8,9,10,11,2,3,4,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5118 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5118_checked : acceptsGraphIso
    (source (graph core5118) (root 7) 2 4) DegreeTwoThreeSpectrum4902.graph sourceMap5118=true := by decide +kernel
theorem fusedMap5118_checked : acceptsGraphIso
    (fused (graph core5118) (root 7) 2 4) DegreeTwoThreeSpectrum4207.graph fusedMap5118=true := by decide +kernel
theorem certified5118 : Certified (graph core5118) (root 7) 2 4 :=
  of_native_maps core5118 DegreeTwoThreeSpectrum4902.graph DegreeTwoThreeSpectrum4207.graph
    sourceMap5118 fusedMap5118 sourceMap5118_checked fusedMap5118_checked
    DegreeTwoThreeFiniteComparisons.comparison5118
#print axioms sourceMap5118_checked
#print axioms fusedMap5118_checked
#print axioms certified5118
def sourceMap5118swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,5,6,7,8,9,10,11,0,12,13,14,15,2,3,4] (sourceLabel 7 4 2 v)
def fusedMap5118swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5118swap_checked : acceptsGraphIso
    (source (graph core5118) (root 7) 4 2) DegreeTwoThreeSpectrum4902.graph sourceMap5118swap=true := by decide +kernel
theorem fusedMap5118swap_checked : acceptsGraphIso
    (fused (graph core5118) (root 7) 4 2) DegreeTwoThreeSpectrum4207.graph fusedMap5118swap=true := by decide +kernel
theorem certified5118swap : Certified (graph core5118) (root 7) 4 2 :=
  of_native_maps core5118 DegreeTwoThreeSpectrum4902.graph DegreeTwoThreeSpectrum4207.graph
    sourceMap5118swap fusedMap5118swap sourceMap5118swap_checked fusedMap5118swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5118
#print axioms sourceMap5118swap_checked
#print axioms fusedMap5118swap_checked
#print axioms certified5118swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
