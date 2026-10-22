/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1798 : Family 10 := level10.get ⟨1131,by decide⟩
def sourceMap1798 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1798 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1798_checked : acceptsGraphIso
    (source (graph core1798) (root 10) 0 2) DegreeTwoThreeSpectrum3212.graph sourceMap1798=true := by decide +kernel
theorem fusedMap1798_checked : acceptsGraphIso
    (fused (graph core1798) (root 10) 0 2) DegreeTwoThreeSpectrum3213.graph fusedMap1798=true := by decide +kernel
theorem certified1798 : Certified (graph core1798) (root 10) 0 2 :=
  of_native_maps core1798 DegreeTwoThreeSpectrum3212.graph DegreeTwoThreeSpectrum3213.graph
    sourceMap1798 fusedMap1798 sourceMap1798_checked fusedMap1798_checked
    DegreeTwoThreeFiniteComparisons.comparison1798
#print axioms sourceMap1798_checked
#print axioms fusedMap1798_checked
#print axioms certified1798
def sourceMap1798swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1798swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1798swap_checked : acceptsGraphIso
    (source (graph core1798) (root 10) 2 0) DegreeTwoThreeSpectrum3212.graph sourceMap1798swap=true := by decide +kernel
theorem fusedMap1798swap_checked : acceptsGraphIso
    (fused (graph core1798) (root 10) 2 0) DegreeTwoThreeSpectrum3213.graph fusedMap1798swap=true := by decide +kernel
theorem certified1798swap : Certified (graph core1798) (root 10) 2 0 :=
  of_native_maps core1798 DegreeTwoThreeSpectrum3212.graph DegreeTwoThreeSpectrum3213.graph
    sourceMap1798swap fusedMap1798swap sourceMap1798swap_checked fusedMap1798swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1798
#print axioms sourceMap1798swap_checked
#print axioms fusedMap1798swap_checked
#print axioms certified1798swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
