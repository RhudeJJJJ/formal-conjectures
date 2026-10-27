/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3981 : Family 7 := level7.get ⟨90,by decide⟩
def sourceMap3981 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3981 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3981_checked : acceptsGraphIso
    (source (graph core3981) (root 7) 1 5) DegreeTwoThreeSpectrum4483.graph sourceMap3981=true := by decide +kernel
theorem fusedMap3981_checked : acceptsGraphIso
    (fused (graph core3981) (root 7) 1 5) DegreeTwoThreeSpectrum4018.graph fusedMap3981=true := by decide +kernel
theorem certified3981 : Certified (graph core3981) (root 7) 1 5 :=
  of_native_maps core3981 DegreeTwoThreeSpectrum4483.graph DegreeTwoThreeSpectrum4018.graph
    sourceMap3981 fusedMap3981 sourceMap3981_checked fusedMap3981_checked
    DegreeTwoThreeFiniteComparisons.comparison3981
#print axioms sourceMap3981_checked
#print axioms fusedMap3981_checked
#print axioms certified3981
def sourceMap3981swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3981swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3981swap_checked : acceptsGraphIso
    (source (graph core3981) (root 7) 5 1) DegreeTwoThreeSpectrum4483.graph sourceMap3981swap=true := by decide +kernel
theorem fusedMap3981swap_checked : acceptsGraphIso
    (fused (graph core3981) (root 7) 5 1) DegreeTwoThreeSpectrum4018.graph fusedMap3981swap=true := by decide +kernel
theorem certified3981swap : Certified (graph core3981) (root 7) 5 1 :=
  of_native_maps core3981 DegreeTwoThreeSpectrum4483.graph DegreeTwoThreeSpectrum4018.graph
    sourceMap3981swap fusedMap3981swap sourceMap3981swap_checked fusedMap3981swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3981
#print axioms sourceMap3981swap_checked
#print axioms fusedMap3981swap_checked
#print axioms certified3981swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
