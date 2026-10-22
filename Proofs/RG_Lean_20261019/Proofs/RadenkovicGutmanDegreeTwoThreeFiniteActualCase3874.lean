/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3874 : Family 8 := level8.get ⟨155,by decide⟩
def sourceMap3874 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3874 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3874_checked : acceptsGraphIso
    (source (graph core3874) (root 8) 1 4) DegreeTwoThreeSpectrum4511.graph sourceMap3874=true := by decide +kernel
theorem fusedMap3874_checked : acceptsGraphIso
    (fused (graph core3874) (root 8) 1 4) DegreeTwoThreeSpectrum4027.graph fusedMap3874=true := by decide +kernel
theorem certified3874 : Certified (graph core3874) (root 8) 1 4 :=
  of_native_maps core3874 DegreeTwoThreeSpectrum4511.graph DegreeTwoThreeSpectrum4027.graph
    sourceMap3874 fusedMap3874 sourceMap3874_checked fusedMap3874_checked
    DegreeTwoThreeFiniteComparisons.comparison3874
#print axioms sourceMap3874_checked
#print axioms fusedMap3874_checked
#print axioms certified3874
def sourceMap3874swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3874swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3874swap_checked : acceptsGraphIso
    (source (graph core3874) (root 8) 4 1) DegreeTwoThreeSpectrum4511.graph sourceMap3874swap=true := by decide +kernel
theorem fusedMap3874swap_checked : acceptsGraphIso
    (fused (graph core3874) (root 8) 4 1) DegreeTwoThreeSpectrum4027.graph fusedMap3874swap=true := by decide +kernel
theorem certified3874swap : Certified (graph core3874) (root 8) 4 1 :=
  of_native_maps core3874 DegreeTwoThreeSpectrum4511.graph DegreeTwoThreeSpectrum4027.graph
    sourceMap3874swap fusedMap3874swap sourceMap3874swap_checked fusedMap3874swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3874
#print axioms sourceMap3874swap_checked
#print axioms fusedMap3874swap_checked
#print axioms certified3874swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
