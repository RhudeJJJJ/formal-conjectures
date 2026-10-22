/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3020 : Family 10 := level10.get ⟨1618,by decide⟩
def sourceMap3020 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3020 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3020_checked : acceptsGraphIso
    (source (graph core3020) (root 10) 0 4) DegreeTwoThreeSpectrum7175.graph sourceMap3020=true := by decide +kernel
theorem fusedMap3020_checked : acceptsGraphIso
    (fused (graph core3020) (root 10) 0 4) DegreeTwoThreeSpectrum6173.graph fusedMap3020=true := by decide +kernel
theorem certified3020 : Certified (graph core3020) (root 10) 0 4 :=
  of_native_maps core3020 DegreeTwoThreeSpectrum7175.graph DegreeTwoThreeSpectrum6173.graph
    sourceMap3020 fusedMap3020 sourceMap3020_checked fusedMap3020_checked
    DegreeTwoThreeFiniteComparisons.comparison3020
#print axioms sourceMap3020_checked
#print axioms fusedMap3020_checked
#print axioms certified3020
def sourceMap3020swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3020swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3020swap_checked : acceptsGraphIso
    (source (graph core3020) (root 10) 4 0) DegreeTwoThreeSpectrum7175.graph sourceMap3020swap=true := by decide +kernel
theorem fusedMap3020swap_checked : acceptsGraphIso
    (fused (graph core3020) (root 10) 4 0) DegreeTwoThreeSpectrum6173.graph fusedMap3020swap=true := by decide +kernel
theorem certified3020swap : Certified (graph core3020) (root 10) 4 0 :=
  of_native_maps core3020 DegreeTwoThreeSpectrum7175.graph DegreeTwoThreeSpectrum6173.graph
    sourceMap3020swap fusedMap3020swap sourceMap3020swap_checked fusedMap3020swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3020
#print axioms sourceMap3020swap_checked
#print axioms fusedMap3020swap_checked
#print axioms certified3020swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
