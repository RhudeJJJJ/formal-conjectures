/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1932 : Family 10 := level10.get ⟨1446,by decide⟩
def sourceMap1932 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,4,5,6,7,1,2,3] (sourceLabel 10 0 2 v)
def fusedMap1932 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1932_checked : acceptsGraphIso
    (source (graph core1932) (root 10) 0 2) DegreeTwoThreeSpectrum3655.graph sourceMap1932=true := by decide +kernel
theorem fusedMap1932_checked : acceptsGraphIso
    (fused (graph core1932) (root 10) 0 2) DegreeTwoThreeSpectrum3684.graph fusedMap1932=true := by decide +kernel
theorem certified1932 : Certified (graph core1932) (root 10) 0 2 :=
  of_native_maps core1932 DegreeTwoThreeSpectrum3655.graph DegreeTwoThreeSpectrum3684.graph
    sourceMap1932 fusedMap1932 sourceMap1932_checked fusedMap1932_checked
    DegreeTwoThreeFiniteComparisons.comparison1932
#print axioms sourceMap1932_checked
#print axioms fusedMap1932_checked
#print axioms certified1932
def sourceMap1932swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,4,5,6,1,2,3,7] (sourceLabel 10 2 0 v)
def fusedMap1932swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1932swap_checked : acceptsGraphIso
    (source (graph core1932) (root 10) 2 0) DegreeTwoThreeSpectrum3655.graph sourceMap1932swap=true := by decide +kernel
theorem fusedMap1932swap_checked : acceptsGraphIso
    (fused (graph core1932) (root 10) 2 0) DegreeTwoThreeSpectrum3684.graph fusedMap1932swap=true := by decide +kernel
theorem certified1932swap : Certified (graph core1932) (root 10) 2 0 :=
  of_native_maps core1932 DegreeTwoThreeSpectrum3655.graph DegreeTwoThreeSpectrum3684.graph
    sourceMap1932swap fusedMap1932swap sourceMap1932swap_checked fusedMap1932swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1932
#print axioms sourceMap1932swap_checked
#print axioms fusedMap1932swap_checked
#print axioms certified1932swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
