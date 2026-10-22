/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1997 : Family 10 := level10.get ⟨1618,by decide⟩
def sourceMap1997 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1997 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1997_checked : acceptsGraphIso
    (source (graph core1997) (root 10) 0 2) DegreeTwoThreeSpectrum3784.graph sourceMap1997=true := by decide +kernel
theorem fusedMap1997_checked : acceptsGraphIso
    (fused (graph core1997) (root 10) 0 2) DegreeTwoThreeSpectrum3159.graph fusedMap1997=true := by decide +kernel
theorem certified1997 : Certified (graph core1997) (root 10) 0 2 :=
  of_native_maps core1997 DegreeTwoThreeSpectrum3784.graph DegreeTwoThreeSpectrum3159.graph
    sourceMap1997 fusedMap1997 sourceMap1997_checked fusedMap1997_checked
    DegreeTwoThreeFiniteComparisons.comparison1997
#print axioms sourceMap1997_checked
#print axioms fusedMap1997_checked
#print axioms certified1997
def sourceMap1997swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1997swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1997swap_checked : acceptsGraphIso
    (source (graph core1997) (root 10) 2 0) DegreeTwoThreeSpectrum3784.graph sourceMap1997swap=true := by decide +kernel
theorem fusedMap1997swap_checked : acceptsGraphIso
    (fused (graph core1997) (root 10) 2 0) DegreeTwoThreeSpectrum3159.graph fusedMap1997swap=true := by decide +kernel
theorem certified1997swap : Certified (graph core1997) (root 10) 2 0 :=
  of_native_maps core1997 DegreeTwoThreeSpectrum3784.graph DegreeTwoThreeSpectrum3159.graph
    sourceMap1997swap fusedMap1997swap sourceMap1997swap_checked fusedMap1997swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1997
#print axioms sourceMap1997swap_checked
#print axioms fusedMap1997swap_checked
#print axioms certified1997swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
