/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3994 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap3994 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,9,7,8,1,0,10,11,12,13,14] (sourceLabel 5 1 6 v)
def fusedMap3994 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 1 6 v)
theorem sourceMap3994_checked : acceptsGraphIso
    (source (graph core3994) (root 5) 1 6) DegreeTwoThreeSpectrum2741.graph sourceMap3994=true := by decide +kernel
theorem fusedMap3994_checked : acceptsGraphIso
    (fused (graph core3994) (root 5) 1 6) DegreeTwoThreeSpectrum2365.graph fusedMap3994=true := by decide +kernel
theorem certified3994 : Certified (graph core3994) (root 5) 1 6 :=
  of_native_maps core3994 DegreeTwoThreeSpectrum2741.graph DegreeTwoThreeSpectrum2365.graph
    sourceMap3994 fusedMap3994 sourceMap3994_checked fusedMap3994_checked
    DegreeTwoThreeFiniteComparisons.comparison3994
#print axioms sourceMap3994_checked
#print axioms fusedMap3994_checked
#print axioms certified3994
def sourceMap3994swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 2) → Fin 15 :=
  fun v => ![2,3,4,5,6,9,1,0,10,11,12,13,14,7,8] (sourceLabel 5 6 1 v)
def fusedMap3994swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 6 1 v)
theorem sourceMap3994swap_checked : acceptsGraphIso
    (source (graph core3994) (root 5) 6 1) DegreeTwoThreeSpectrum2741.graph sourceMap3994swap=true := by decide +kernel
theorem fusedMap3994swap_checked : acceptsGraphIso
    (fused (graph core3994) (root 5) 6 1) DegreeTwoThreeSpectrum2365.graph fusedMap3994swap=true := by decide +kernel
theorem certified3994swap : Certified (graph core3994) (root 5) 6 1 :=
  of_native_maps core3994 DegreeTwoThreeSpectrum2741.graph DegreeTwoThreeSpectrum2365.graph
    sourceMap3994swap fusedMap3994swap sourceMap3994swap_checked fusedMap3994swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3994
#print axioms sourceMap3994swap_checked
#print axioms fusedMap3994swap_checked
#print axioms certified3994swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
