/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3786 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap3786 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3786 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3786_checked : acceptsGraphIso
    (source (graph core3786) (root 6) 1 4) DegreeTwoThreeSpectrum2196.graph sourceMap3786=true := by decide +kernel
theorem fusedMap3786_checked : acceptsGraphIso
    (fused (graph core3786) (root 6) 1 4) DegreeTwoThreeSpectrum1865.graph fusedMap3786=true := by decide +kernel
theorem certified3786 : Certified (graph core3786) (root 6) 1 4 :=
  of_native_maps core3786 DegreeTwoThreeSpectrum2196.graph DegreeTwoThreeSpectrum1865.graph
    sourceMap3786 fusedMap3786 sourceMap3786_checked fusedMap3786_checked
    DegreeTwoThreeFiniteComparisons.comparison3786
#print axioms sourceMap3786_checked
#print axioms fusedMap3786_checked
#print axioms certified3786
def sourceMap3786swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,10,11,12,13,8,9] (sourceLabel 6 4 1 v)
def fusedMap3786swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3786swap_checked : acceptsGraphIso
    (source (graph core3786) (root 6) 4 1) DegreeTwoThreeSpectrum2196.graph sourceMap3786swap=true := by decide +kernel
theorem fusedMap3786swap_checked : acceptsGraphIso
    (fused (graph core3786) (root 6) 4 1) DegreeTwoThreeSpectrum1865.graph fusedMap3786swap=true := by decide +kernel
theorem certified3786swap : Certified (graph core3786) (root 6) 4 1 :=
  of_native_maps core3786 DegreeTwoThreeSpectrum2196.graph DegreeTwoThreeSpectrum1865.graph
    sourceMap3786swap fusedMap3786swap sourceMap3786swap_checked fusedMap3786swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3786
#print axioms sourceMap3786swap_checked
#print axioms fusedMap3786swap_checked
#print axioms certified3786swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
