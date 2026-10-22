/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3263 : Family 9 := level9.get ⟨122,by decide⟩
def sourceMap3263 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3263 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3263_checked : acceptsGraphIso
    (source (graph core3263) (root 9) 0 5) DegreeTwoThreeSpectrum5901.graph sourceMap3263=true := by decide +kernel
theorem fusedMap3263_checked : acceptsGraphIso
    (fused (graph core3263) (root 9) 0 5) DegreeTwoThreeSpectrum5094.graph fusedMap3263=true := by decide +kernel
theorem certified3263 : Certified (graph core3263) (root 9) 0 5 :=
  of_native_maps core3263 DegreeTwoThreeSpectrum5901.graph DegreeTwoThreeSpectrum5094.graph
    sourceMap3263 fusedMap3263 sourceMap3263_checked fusedMap3263_checked
    DegreeTwoThreeFiniteComparisons.comparison3263
#print axioms sourceMap3263_checked
#print axioms fusedMap3263_checked
#print axioms certified3263
def sourceMap3263swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3263swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3263swap_checked : acceptsGraphIso
    (source (graph core3263) (root 9) 5 0) DegreeTwoThreeSpectrum5901.graph sourceMap3263swap=true := by decide +kernel
theorem fusedMap3263swap_checked : acceptsGraphIso
    (fused (graph core3263) (root 9) 5 0) DegreeTwoThreeSpectrum5094.graph fusedMap3263swap=true := by decide +kernel
theorem certified3263swap : Certified (graph core3263) (root 9) 5 0 :=
  of_native_maps core3263 DegreeTwoThreeSpectrum5901.graph DegreeTwoThreeSpectrum5094.graph
    sourceMap3263swap fusedMap3263swap sourceMap3263swap_checked fusedMap3263swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3263
#print axioms sourceMap3263swap_checked
#print axioms fusedMap3263swap_checked
#print axioms certified3263swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
