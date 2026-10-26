/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3854 : Family 8 := level8.get ⟨102,by decide⟩
def sourceMap3854 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3854 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3854_checked : acceptsGraphIso
    (source (graph core3854) (root 8) 1 4) DegreeTwoThreeSpectrum4229.graph sourceMap3854=true := by decide +kernel
theorem fusedMap3854_checked : acceptsGraphIso
    (fused (graph core3854) (root 8) 1 4) DegreeTwoThreeSpectrum3900.graph fusedMap3854=true := by decide +kernel
theorem certified3854 : Certified (graph core3854) (root 8) 1 4 :=
  of_native_maps core3854 DegreeTwoThreeSpectrum4229.graph DegreeTwoThreeSpectrum3900.graph
    sourceMap3854 fusedMap3854 sourceMap3854_checked fusedMap3854_checked
    DegreeTwoThreeFiniteComparisons.comparison3854
#print axioms sourceMap3854_checked
#print axioms fusedMap3854_checked
#print axioms certified3854
def sourceMap3854swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3854swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3854swap_checked : acceptsGraphIso
    (source (graph core3854) (root 8) 4 1) DegreeTwoThreeSpectrum4229.graph sourceMap3854swap=true := by decide +kernel
theorem fusedMap3854swap_checked : acceptsGraphIso
    (fused (graph core3854) (root 8) 4 1) DegreeTwoThreeSpectrum3900.graph fusedMap3854swap=true := by decide +kernel
theorem certified3854swap : Certified (graph core3854) (root 8) 4 1 :=
  of_native_maps core3854 DegreeTwoThreeSpectrum4229.graph DegreeTwoThreeSpectrum3900.graph
    sourceMap3854swap fusedMap3854swap sourceMap3854swap_checked fusedMap3854swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3854
#print axioms sourceMap3854swap_checked
#print axioms fusedMap3854swap_checked
#print axioms certified3854swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
