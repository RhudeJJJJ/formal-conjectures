/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3875 : Family 8 := level8.get ⟨157,by decide⟩
def sourceMap3875 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3875 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3875_checked : acceptsGraphIso
    (source (graph core3875) (root 8) 1 4) DegreeTwoThreeSpectrum4522.graph sourceMap3875=true := by decide +kernel
theorem fusedMap3875_checked : acceptsGraphIso
    (fused (graph core3875) (root 8) 1 4) DegreeTwoThreeSpectrum4036.graph fusedMap3875=true := by decide +kernel
theorem certified3875 : Certified (graph core3875) (root 8) 1 4 :=
  of_native_maps core3875 DegreeTwoThreeSpectrum4522.graph DegreeTwoThreeSpectrum4036.graph
    sourceMap3875 fusedMap3875 sourceMap3875_checked fusedMap3875_checked
    DegreeTwoThreeFiniteComparisons.comparison3875
#print axioms sourceMap3875_checked
#print axioms fusedMap3875_checked
#print axioms certified3875
def sourceMap3875swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3875swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3875swap_checked : acceptsGraphIso
    (source (graph core3875) (root 8) 4 1) DegreeTwoThreeSpectrum4522.graph sourceMap3875swap=true := by decide +kernel
theorem fusedMap3875swap_checked : acceptsGraphIso
    (fused (graph core3875) (root 8) 4 1) DegreeTwoThreeSpectrum4036.graph fusedMap3875swap=true := by decide +kernel
theorem certified3875swap : Certified (graph core3875) (root 8) 4 1 :=
  of_native_maps core3875 DegreeTwoThreeSpectrum4522.graph DegreeTwoThreeSpectrum4036.graph
    sourceMap3875swap fusedMap3875swap sourceMap3875swap_checked fusedMap3875swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3875
#print axioms sourceMap3875swap_checked
#print axioms fusedMap3875swap_checked
#print axioms certified3875swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
