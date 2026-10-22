/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3145 : Family 8 := level8.get ⟨31,by decide⟩
def sourceMap3145 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (sourceLabel 8 0 5 v)
def fusedMap3145 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3145_checked : acceptsGraphIso
    (source (graph core3145) (root 8) 0 5) DegreeTwoThreeSpectrum4167.graph sourceMap3145=true := by decide +kernel
theorem fusedMap3145_checked : acceptsGraphIso
    (fused (graph core3145) (root 8) 0 5) DegreeTwoThreeSpectrum3885.graph fusedMap3145=true := by decide +kernel
theorem certified3145 : Certified (graph core3145) (root 8) 0 5 :=
  of_native_maps core3145 DegreeTwoThreeSpectrum4167.graph DegreeTwoThreeSpectrum3885.graph
    sourceMap3145 fusedMap3145 sourceMap3145_checked fusedMap3145_checked
    DegreeTwoThreeFiniteComparisons.comparison3145
#print axioms sourceMap3145_checked
#print axioms fusedMap3145_checked
#print axioms certified3145
def sourceMap3145swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13,15] (sourceLabel 8 5 0 v)
def fusedMap3145swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3145swap_checked : acceptsGraphIso
    (source (graph core3145) (root 8) 5 0) DegreeTwoThreeSpectrum4167.graph sourceMap3145swap=true := by decide +kernel
theorem fusedMap3145swap_checked : acceptsGraphIso
    (fused (graph core3145) (root 8) 5 0) DegreeTwoThreeSpectrum3885.graph fusedMap3145swap=true := by decide +kernel
theorem certified3145swap : Certified (graph core3145) (root 8) 5 0 :=
  of_native_maps core3145 DegreeTwoThreeSpectrum4167.graph DegreeTwoThreeSpectrum3885.graph
    sourceMap3145swap fusedMap3145swap sourceMap3145swap_checked fusedMap3145swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3145
#print axioms sourceMap3145swap_checked
#print axioms fusedMap3145swap_checked
#print axioms certified3145swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
