/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3483 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap3483 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (sourceLabel 5 0 6 v)
def fusedMap3483 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 0 6 v)
theorem sourceMap3483_checked : acceptsGraphIso
    (source (graph core3483) (root 5) 0 6) DegreeTwoThreeSpectrum1870.graph sourceMap3483=true := by decide +kernel
theorem fusedMap3483_checked : acceptsGraphIso
    (fused (graph core3483) (root 5) 0 6) DegreeTwoThreeSpectrum1723.graph fusedMap3483=true := by decide +kernel
theorem certified3483 : Certified (graph core3483) (root 5) 0 6 :=
  of_native_maps core3483 DegreeTwoThreeSpectrum1870.graph DegreeTwoThreeSpectrum1723.graph
    sourceMap3483 fusedMap3483 sourceMap3483_checked fusedMap3483_checked
    DegreeTwoThreeFiniteComparisons.comparison3483
#print axioms sourceMap3483_checked
#print axioms fusedMap3483_checked
#print axioms certified3483
def sourceMap3483swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,13,8] (sourceLabel 5 6 0 v)
def fusedMap3483swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 6 0 v)
theorem sourceMap3483swap_checked : acceptsGraphIso
    (source (graph core3483) (root 5) 6 0) DegreeTwoThreeSpectrum1870.graph sourceMap3483swap=true := by decide +kernel
theorem fusedMap3483swap_checked : acceptsGraphIso
    (fused (graph core3483) (root 5) 6 0) DegreeTwoThreeSpectrum1723.graph fusedMap3483swap=true := by decide +kernel
theorem certified3483swap : Certified (graph core3483) (root 5) 6 0 :=
  of_native_maps core3483 DegreeTwoThreeSpectrum1870.graph DegreeTwoThreeSpectrum1723.graph
    sourceMap3483swap fusedMap3483swap sourceMap3483swap_checked fusedMap3483swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3483
#print axioms sourceMap3483swap_checked
#print axioms fusedMap3483swap_checked
#print axioms certified3483swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
