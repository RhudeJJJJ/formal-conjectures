/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3644 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap3644 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (sourceLabel 5 0 7 v)
def fusedMap3644 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 0 7 v)
theorem sourceMap3644_checked : acceptsGraphIso
    (source (graph core3644) (root 5) 0 7) DegreeTwoThreeSpectrum2462.graph sourceMap3644=true := by decide +kernel
theorem fusedMap3644_checked : acceptsGraphIso
    (fused (graph core3644) (root 5) 0 7) DegreeTwoThreeSpectrum2315.graph fusedMap3644=true := by decide +kernel
theorem certified3644 : Certified (graph core3644) (root 5) 0 7 :=
  of_native_maps core3644 DegreeTwoThreeSpectrum2462.graph DegreeTwoThreeSpectrum2315.graph
    sourceMap3644 fusedMap3644 sourceMap3644_checked fusedMap3644_checked
    DegreeTwoThreeFiniteComparisons.comparison3644
#print axioms sourceMap3644_checked
#print axioms fusedMap3644_checked
#print axioms certified3644
def sourceMap3644swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 1) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,10,11,12,13,14,9] (sourceLabel 5 7 0 v)
def fusedMap3644swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 7 0 v)
theorem sourceMap3644swap_checked : acceptsGraphIso
    (source (graph core3644) (root 5) 7 0) DegreeTwoThreeSpectrum2462.graph sourceMap3644swap=true := by decide +kernel
theorem fusedMap3644swap_checked : acceptsGraphIso
    (fused (graph core3644) (root 5) 7 0) DegreeTwoThreeSpectrum2315.graph fusedMap3644swap=true := by decide +kernel
theorem certified3644swap : Certified (graph core3644) (root 5) 7 0 :=
  of_native_maps core3644 DegreeTwoThreeSpectrum2462.graph DegreeTwoThreeSpectrum2315.graph
    sourceMap3644swap fusedMap3644swap sourceMap3644swap_checked fusedMap3644swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3644
#print axioms sourceMap3644swap_checked
#print axioms fusedMap3644swap_checked
#print axioms certified3644swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
