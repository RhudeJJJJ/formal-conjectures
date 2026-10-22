/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3989 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap3989 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,8,6,7,1,0,9,10,11,12,13] (sourceLabel 4 1 6 v)
def fusedMap3989 : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 1 6 v)
theorem sourceMap3989_checked : acceptsGraphIso
    (source (graph core3989) (root 4) 1 6) DegreeTwoThreeSpectrum1870.graph sourceMap3989=true := by decide +kernel
theorem fusedMap3989_checked : acceptsGraphIso
    (fused (graph core3989) (root 4) 1 6) DegreeTwoThreeSpectrum1728.graph fusedMap3989=true := by decide +kernel
theorem certified3989 : Certified (graph core3989) (root 4) 1 6 :=
  of_native_maps core3989 DegreeTwoThreeSpectrum1870.graph DegreeTwoThreeSpectrum1728.graph
    sourceMap3989 fusedMap3989 sourceMap3989_checked fusedMap3989_checked
    DegreeTwoThreeFiniteComparisons.comparison3989
#print axioms sourceMap3989_checked
#print axioms fusedMap3989_checked
#print axioms certified3989
def sourceMap3989swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 2) → Fin 14 :=
  fun v => ![2,3,4,5,8,1,0,9,10,11,12,13,6,7] (sourceLabel 4 6 1 v)
def fusedMap3989swap : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 6 1 v)
theorem sourceMap3989swap_checked : acceptsGraphIso
    (source (graph core3989) (root 4) 6 1) DegreeTwoThreeSpectrum1870.graph sourceMap3989swap=true := by decide +kernel
theorem fusedMap3989swap_checked : acceptsGraphIso
    (fused (graph core3989) (root 4) 6 1) DegreeTwoThreeSpectrum1728.graph fusedMap3989swap=true := by decide +kernel
theorem certified3989swap : Certified (graph core3989) (root 4) 6 1 :=
  of_native_maps core3989 DegreeTwoThreeSpectrum1870.graph DegreeTwoThreeSpectrum1728.graph
    sourceMap3989swap fusedMap3989swap sourceMap3989swap_checked fusedMap3989swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3989
#print axioms sourceMap3989swap_checked
#print axioms fusedMap3989swap_checked
#print axioms certified3989swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
