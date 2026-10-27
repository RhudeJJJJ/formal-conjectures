/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3976 : Family 7 := level7.get ⟨78,by decide⟩
def sourceMap3976 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3976 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3976_checked : acceptsGraphIso
    (source (graph core3976) (root 7) 1 5) DegreeTwoThreeSpectrum4342.graph sourceMap3976=true := by decide +kernel
theorem fusedMap3976_checked : acceptsGraphIso
    (fused (graph core3976) (root 7) 1 5) DegreeTwoThreeSpectrum3942.graph fusedMap3976=true := by decide +kernel
theorem certified3976 : Certified (graph core3976) (root 7) 1 5 :=
  of_native_maps core3976 DegreeTwoThreeSpectrum4342.graph DegreeTwoThreeSpectrum3942.graph
    sourceMap3976 fusedMap3976 sourceMap3976_checked fusedMap3976_checked
    DegreeTwoThreeFiniteComparisons.comparison3976
#print axioms sourceMap3976_checked
#print axioms fusedMap3976_checked
#print axioms certified3976
def sourceMap3976swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3976swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3976swap_checked : acceptsGraphIso
    (source (graph core3976) (root 7) 5 1) DegreeTwoThreeSpectrum4342.graph sourceMap3976swap=true := by decide +kernel
theorem fusedMap3976swap_checked : acceptsGraphIso
    (fused (graph core3976) (root 7) 5 1) DegreeTwoThreeSpectrum3942.graph fusedMap3976swap=true := by decide +kernel
theorem certified3976swap : Certified (graph core3976) (root 7) 5 1 :=
  of_native_maps core3976 DegreeTwoThreeSpectrum4342.graph DegreeTwoThreeSpectrum3942.graph
    sourceMap3976swap fusedMap3976swap sourceMap3976swap_checked fusedMap3976swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3976
#print axioms sourceMap3976swap_checked
#print axioms fusedMap3976swap_checked
#print axioms certified3976swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
