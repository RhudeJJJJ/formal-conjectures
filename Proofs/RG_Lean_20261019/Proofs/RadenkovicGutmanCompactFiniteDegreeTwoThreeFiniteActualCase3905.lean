/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3905 : Family 8 := level8.get ⟨223,by decide⟩
def sourceMap3905 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3905 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3905_checked : acceptsGraphIso
    (source (graph core3905) (root 8) 1 4) DegreeTwoThreeSpectrum4761.graph sourceMap3905=true := by decide +kernel
theorem fusedMap3905_checked : acceptsGraphIso
    (fused (graph core3905) (root 8) 1 4) DegreeTwoThreeSpectrum4334.graph fusedMap3905=true := by decide +kernel
theorem certified3905 : Certified (graph core3905) (root 8) 1 4 :=
  of_native_maps core3905 DegreeTwoThreeSpectrum4761.graph DegreeTwoThreeSpectrum4334.graph
    sourceMap3905 fusedMap3905 sourceMap3905_checked fusedMap3905_checked
    DegreeTwoThreeFiniteComparisons.comparison3905
#print axioms sourceMap3905_checked
#print axioms fusedMap3905_checked
#print axioms certified3905
def sourceMap3905swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3905swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3905swap_checked : acceptsGraphIso
    (source (graph core3905) (root 8) 4 1) DegreeTwoThreeSpectrum4761.graph sourceMap3905swap=true := by decide +kernel
theorem fusedMap3905swap_checked : acceptsGraphIso
    (fused (graph core3905) (root 8) 4 1) DegreeTwoThreeSpectrum4334.graph fusedMap3905swap=true := by decide +kernel
theorem certified3905swap : Certified (graph core3905) (root 8) 4 1 :=
  of_native_maps core3905 DegreeTwoThreeSpectrum4761.graph DegreeTwoThreeSpectrum4334.graph
    sourceMap3905swap fusedMap3905swap sourceMap3905swap_checked fusedMap3905swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3905
#print axioms sourceMap3905swap_checked
#print axioms fusedMap3905swap_checked
#print axioms certified3905swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
