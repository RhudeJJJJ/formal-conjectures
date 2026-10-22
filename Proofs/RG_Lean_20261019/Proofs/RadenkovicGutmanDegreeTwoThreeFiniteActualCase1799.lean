/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1799 : Family 10 := level10.get ⟨1132,by decide⟩
def sourceMap1799 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1799 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1799_checked : acceptsGraphIso
    (source (graph core1799) (root 10) 0 2) DegreeTwoThreeSpectrum3214.graph sourceMap1799=true := by decide +kernel
theorem fusedMap1799_checked : acceptsGraphIso
    (fused (graph core1799) (root 10) 0 2) DegreeTwoThreeSpectrum3216.graph fusedMap1799=true := by decide +kernel
theorem certified1799 : Certified (graph core1799) (root 10) 0 2 :=
  of_native_maps core1799 DegreeTwoThreeSpectrum3214.graph DegreeTwoThreeSpectrum3216.graph
    sourceMap1799 fusedMap1799 sourceMap1799_checked fusedMap1799_checked
    DegreeTwoThreeFiniteComparisons.comparison1799
#print axioms sourceMap1799_checked
#print axioms fusedMap1799_checked
#print axioms certified1799
def sourceMap1799swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1799swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1799swap_checked : acceptsGraphIso
    (source (graph core1799) (root 10) 2 0) DegreeTwoThreeSpectrum3214.graph sourceMap1799swap=true := by decide +kernel
theorem fusedMap1799swap_checked : acceptsGraphIso
    (fused (graph core1799) (root 10) 2 0) DegreeTwoThreeSpectrum3216.graph fusedMap1799swap=true := by decide +kernel
theorem certified1799swap : Certified (graph core1799) (root 10) 2 0 :=
  of_native_maps core1799 DegreeTwoThreeSpectrum3214.graph DegreeTwoThreeSpectrum3216.graph
    sourceMap1799swap fusedMap1799swap sourceMap1799swap_checked fusedMap1799swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1799
#print axioms sourceMap1799swap_checked
#print axioms fusedMap1799swap_checked
#print axioms certified1799swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
