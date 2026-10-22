/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1835 : Family 10 := level10.get ⟨1214,by decide⟩
def sourceMap1835 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1835 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1835_checked : acceptsGraphIso
    (source (graph core1835) (root 10) 0 2) DegreeTwoThreeSpectrum3336.graph sourceMap1835=true := by decide +kernel
theorem fusedMap1835_checked : acceptsGraphIso
    (fused (graph core1835) (root 10) 0 2) DegreeTwoThreeSpectrum3346.graph fusedMap1835=true := by decide +kernel
theorem certified1835 : Certified (graph core1835) (root 10) 0 2 :=
  of_native_maps core1835 DegreeTwoThreeSpectrum3336.graph DegreeTwoThreeSpectrum3346.graph
    sourceMap1835 fusedMap1835 sourceMap1835_checked fusedMap1835_checked
    DegreeTwoThreeFiniteComparisons.comparison1835
#print axioms sourceMap1835_checked
#print axioms fusedMap1835_checked
#print axioms certified1835
def sourceMap1835swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1835swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1835swap_checked : acceptsGraphIso
    (source (graph core1835) (root 10) 2 0) DegreeTwoThreeSpectrum3336.graph sourceMap1835swap=true := by decide +kernel
theorem fusedMap1835swap_checked : acceptsGraphIso
    (fused (graph core1835) (root 10) 2 0) DegreeTwoThreeSpectrum3346.graph fusedMap1835swap=true := by decide +kernel
theorem certified1835swap : Certified (graph core1835) (root 10) 2 0 :=
  of_native_maps core1835 DegreeTwoThreeSpectrum3336.graph DegreeTwoThreeSpectrum3346.graph
    sourceMap1835swap fusedMap1835swap sourceMap1835swap_checked fusedMap1835swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1835
#print axioms sourceMap1835swap_checked
#print axioms fusedMap1835swap_checked
#print axioms certified1835swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
