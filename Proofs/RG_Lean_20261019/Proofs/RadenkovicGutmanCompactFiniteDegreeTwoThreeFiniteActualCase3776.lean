/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3776 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap3776 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,8,6,7,9,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3776 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3776_checked : acceptsGraphIso
    (source (graph core3776) (root 6) 1 4) DegreeTwoThreeSpectrum1843.graph sourceMap3776=true := by decide +kernel
theorem fusedMap3776_checked : acceptsGraphIso
    (fused (graph core3776) (root 6) 1 4) DegreeTwoThreeSpectrum1719.graph fusedMap3776=true := by decide +kernel
theorem certified3776 : Certified (graph core3776) (root 6) 1 4 :=
  of_native_maps core3776 DegreeTwoThreeSpectrum1843.graph DegreeTwoThreeSpectrum1719.graph
    sourceMap3776 fusedMap3776 sourceMap3776_checked fusedMap3776_checked
    DegreeTwoThreeFiniteComparisons.comparison3776
#print axioms sourceMap3776_checked
#print axioms fusedMap3776_checked
#print axioms certified3776
def sourceMap3776swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,12,13,6,7] (sourceLabel 6 4 1 v)
def fusedMap3776swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3776swap_checked : acceptsGraphIso
    (source (graph core3776) (root 6) 4 1) DegreeTwoThreeSpectrum1843.graph sourceMap3776swap=true := by decide +kernel
theorem fusedMap3776swap_checked : acceptsGraphIso
    (fused (graph core3776) (root 6) 4 1) DegreeTwoThreeSpectrum1719.graph fusedMap3776swap=true := by decide +kernel
theorem certified3776swap : Certified (graph core3776) (root 6) 4 1 :=
  of_native_maps core3776 DegreeTwoThreeSpectrum1843.graph DegreeTwoThreeSpectrum1719.graph
    sourceMap3776swap fusedMap3776swap sourceMap3776swap_checked fusedMap3776swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3776
#print axioms sourceMap3776swap_checked
#print axioms fusedMap3776swap_checked
#print axioms certified3776swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
