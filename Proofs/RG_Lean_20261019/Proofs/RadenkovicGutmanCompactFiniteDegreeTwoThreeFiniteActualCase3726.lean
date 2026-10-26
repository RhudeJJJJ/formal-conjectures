/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3726 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap3726 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 10) → Fin 14 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13] (sourceLabel 2 0 9 v)
def fusedMap3726 : (Vertices 2 ⊕ Fin 11) → Fin 14 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13] (fusedLabel 2 0 9 v)
theorem sourceMap3726_checked : acceptsGraphIso
    (source (graph core3726) (root 2) 0 9) DegreeTwoThreeSpectrum1709.graph sourceMap3726=true := by decide +kernel
theorem fusedMap3726_checked : acceptsGraphIso
    (fused (graph core3726) (root 2) 0 9) DegreeTwoThreeSpectrum1715.graph fusedMap3726=true := by decide +kernel
theorem certified3726 : Certified (graph core3726) (root 2) 0 9 :=
  of_native_maps core3726 DegreeTwoThreeSpectrum1709.graph DegreeTwoThreeSpectrum1715.graph
    sourceMap3726 fusedMap3726 sourceMap3726_checked fusedMap3726_checked
    DegreeTwoThreeFiniteComparisons.comparison3726
#print axioms sourceMap3726_checked
#print axioms fusedMap3726_checked
#print axioms certified3726
def sourceMap3726swap : (Vertices 2 ⊕ Fin 10 ⊕ Fin 1) → Fin 14 :=
  fun v => ![4,5,6,3,2,1,0,8,9,10,11,12,13,7] (sourceLabel 2 9 0 v)
def fusedMap3726swap : (Vertices 2 ⊕ Fin 11) → Fin 14 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13] (fusedLabel 2 9 0 v)
theorem sourceMap3726swap_checked : acceptsGraphIso
    (source (graph core3726) (root 2) 9 0) DegreeTwoThreeSpectrum1709.graph sourceMap3726swap=true := by decide +kernel
theorem fusedMap3726swap_checked : acceptsGraphIso
    (fused (graph core3726) (root 2) 9 0) DegreeTwoThreeSpectrum1715.graph fusedMap3726swap=true := by decide +kernel
theorem certified3726swap : Certified (graph core3726) (root 2) 9 0 :=
  of_native_maps core3726 DegreeTwoThreeSpectrum1709.graph DegreeTwoThreeSpectrum1715.graph
    sourceMap3726swap fusedMap3726swap sourceMap3726swap_checked fusedMap3726swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3726
#print axioms sourceMap3726swap_checked
#print axioms fusedMap3726swap_checked
#print axioms certified3726swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
