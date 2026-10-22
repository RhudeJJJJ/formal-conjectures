/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3615 : Family 8 := level8.get ⟨219,by decide⟩
def sourceMap3615 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3615 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3615_checked : acceptsGraphIso
    (source (graph core3615) (root 8) 0 6) DegreeTwoThreeSpectrum6292.graph sourceMap3615=true := by decide +kernel
theorem fusedMap3615_checked : acceptsGraphIso
    (fused (graph core3615) (root 8) 0 6) DegreeTwoThreeSpectrum5265.graph fusedMap3615=true := by decide +kernel
theorem certified3615 : Certified (graph core3615) (root 8) 0 6 :=
  of_native_maps core3615 DegreeTwoThreeSpectrum6292.graph DegreeTwoThreeSpectrum5265.graph
    sourceMap3615 fusedMap3615 sourceMap3615_checked fusedMap3615_checked
    DegreeTwoThreeFiniteComparisons.comparison3615
#print axioms sourceMap3615_checked
#print axioms fusedMap3615_checked
#print axioms certified3615
def sourceMap3615swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3615swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3615swap_checked : acceptsGraphIso
    (source (graph core3615) (root 8) 6 0) DegreeTwoThreeSpectrum6292.graph sourceMap3615swap=true := by decide +kernel
theorem fusedMap3615swap_checked : acceptsGraphIso
    (fused (graph core3615) (root 8) 6 0) DegreeTwoThreeSpectrum5265.graph fusedMap3615swap=true := by decide +kernel
theorem certified3615swap : Certified (graph core3615) (root 8) 6 0 :=
  of_native_maps core3615 DegreeTwoThreeSpectrum6292.graph DegreeTwoThreeSpectrum5265.graph
    sourceMap3615swap fusedMap3615swap sourceMap3615swap_checked fusedMap3615swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3615
#print axioms sourceMap3615swap_checked
#print axioms fusedMap3615swap_checked
#print axioms certified3615swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
