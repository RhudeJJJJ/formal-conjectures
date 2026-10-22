/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1784 : Family 10 := level10.get ⟨1089,by decide⟩
def sourceMap1784 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,14,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1784 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1784_checked : acceptsGraphIso
    (source (graph core1784) (root 10) 0 2) DegreeTwoThreeSpectrum3147.graph sourceMap1784=true := by decide +kernel
theorem fusedMap1784_checked : acceptsGraphIso
    (fused (graph core1784) (root 10) 0 2) DegreeTwoThreeSpectrum3156.graph fusedMap1784=true := by decide +kernel
theorem certified1784 : Certified (graph core1784) (root 10) 0 2 :=
  of_native_maps core1784 DegreeTwoThreeSpectrum3147.graph DegreeTwoThreeSpectrum3156.graph
    sourceMap1784 fusedMap1784 sourceMap1784_checked fusedMap1784_checked
    DegreeTwoThreeFiniteComparisons.comparison1784
#print axioms sourceMap1784_checked
#print axioms fusedMap1784_checked
#print axioms certified1784
def sourceMap1784swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,7,8,9,14] (sourceLabel 10 2 0 v)
def fusedMap1784swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1784swap_checked : acceptsGraphIso
    (source (graph core1784) (root 10) 2 0) DegreeTwoThreeSpectrum3147.graph sourceMap1784swap=true := by decide +kernel
theorem fusedMap1784swap_checked : acceptsGraphIso
    (fused (graph core1784) (root 10) 2 0) DegreeTwoThreeSpectrum3156.graph fusedMap1784swap=true := by decide +kernel
theorem certified1784swap : Certified (graph core1784) (root 10) 2 0 :=
  of_native_maps core1784 DegreeTwoThreeSpectrum3147.graph DegreeTwoThreeSpectrum3156.graph
    sourceMap1784swap fusedMap1784swap sourceMap1784swap_checked fusedMap1784swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1784
#print axioms sourceMap1784swap_checked
#print axioms fusedMap1784swap_checked
#print axioms certified1784swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
