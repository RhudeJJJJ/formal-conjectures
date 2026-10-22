/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3835 : Family 8 := level8.get ⟨43,by decide⟩
def sourceMap3835 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3835 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3835_checked : acceptsGraphIso
    (source (graph core3835) (root 8) 1 4) DegreeTwoThreeSpectrum4328.graph sourceMap3835=true := by decide +kernel
theorem fusedMap3835_checked : acceptsGraphIso
    (fused (graph core3835) (root 8) 1 4) DegreeTwoThreeSpectrum3938.graph fusedMap3835=true := by decide +kernel
theorem certified3835 : Certified (graph core3835) (root 8) 1 4 :=
  of_native_maps core3835 DegreeTwoThreeSpectrum4328.graph DegreeTwoThreeSpectrum3938.graph
    sourceMap3835 fusedMap3835 sourceMap3835_checked fusedMap3835_checked
    DegreeTwoThreeFiniteComparisons.comparison3835
#print axioms sourceMap3835_checked
#print axioms fusedMap3835_checked
#print axioms certified3835
def sourceMap3835swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3835swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3835swap_checked : acceptsGraphIso
    (source (graph core3835) (root 8) 4 1) DegreeTwoThreeSpectrum4328.graph sourceMap3835swap=true := by decide +kernel
theorem fusedMap3835swap_checked : acceptsGraphIso
    (fused (graph core3835) (root 8) 4 1) DegreeTwoThreeSpectrum3938.graph fusedMap3835swap=true := by decide +kernel
theorem certified3835swap : Certified (graph core3835) (root 8) 4 1 :=
  of_native_maps core3835 DegreeTwoThreeSpectrum4328.graph DegreeTwoThreeSpectrum3938.graph
    sourceMap3835swap fusedMap3835swap sourceMap3835swap_checked fusedMap3835swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3835
#print axioms sourceMap3835swap_checked
#print axioms fusedMap3835swap_checked
#print axioms certified3835swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
