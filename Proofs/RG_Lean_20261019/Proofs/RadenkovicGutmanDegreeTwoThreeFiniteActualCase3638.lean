/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3638 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap3638 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (sourceLabel 4 0 7 v)
def fusedMap3638 : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 0 7 v)
theorem sourceMap3638_checked : acceptsGraphIso
    (source (graph core3638) (root 4) 0 7) DegreeTwoThreeSpectrum1764.graph sourceMap3638=true := by decide +kernel
theorem fusedMap3638_checked : acceptsGraphIso
    (fused (graph core3638) (root 4) 0 7) DegreeTwoThreeSpectrum1710.graph fusedMap3638=true := by decide +kernel
theorem certified3638 : Certified (graph core3638) (root 4) 0 7 :=
  of_native_maps core3638 DegreeTwoThreeSpectrum1764.graph DegreeTwoThreeSpectrum1710.graph
    sourceMap3638 fusedMap3638 sourceMap3638_checked fusedMap3638_checked
    DegreeTwoThreeFiniteComparisons.comparison3638
#print axioms sourceMap3638_checked
#print axioms fusedMap3638_checked
#print axioms certified3638
def sourceMap3638swap : (Vertices 4 ⊕ Fin 8 ⊕ Fin 1) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,9,10,11,12,13,8] (sourceLabel 4 7 0 v)
def fusedMap3638swap : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 7 0 v)
theorem sourceMap3638swap_checked : acceptsGraphIso
    (source (graph core3638) (root 4) 7 0) DegreeTwoThreeSpectrum1764.graph sourceMap3638swap=true := by decide +kernel
theorem fusedMap3638swap_checked : acceptsGraphIso
    (fused (graph core3638) (root 4) 7 0) DegreeTwoThreeSpectrum1710.graph fusedMap3638swap=true := by decide +kernel
theorem certified3638swap : Certified (graph core3638) (root 4) 7 0 :=
  of_native_maps core3638 DegreeTwoThreeSpectrum1764.graph DegreeTwoThreeSpectrum1710.graph
    sourceMap3638swap fusedMap3638swap sourceMap3638swap_checked fusedMap3638swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3638
#print axioms sourceMap3638swap_checked
#print axioms fusedMap3638swap_checked
#print axioms certified3638swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
