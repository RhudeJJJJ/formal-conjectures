/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2954 : Family 10 := level10.get ⟨1445,by decide⟩
def sourceMap2954 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2954 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2954_checked : acceptsGraphIso
    (source (graph core2954) (root 10) 0 4) DegreeTwoThreeSpectrum6908.graph sourceMap2954=true := by decide +kernel
theorem fusedMap2954_checked : acceptsGraphIso
    (fused (graph core2954) (root 10) 0 4) DegreeTwoThreeSpectrum6909.graph fusedMap2954=true := by decide +kernel
theorem certified2954 : Certified (graph core2954) (root 10) 0 4 :=
  of_native_maps core2954 DegreeTwoThreeSpectrum6908.graph DegreeTwoThreeSpectrum6909.graph
    sourceMap2954 fusedMap2954 sourceMap2954_checked fusedMap2954_checked
    DegreeTwoThreeFiniteComparisons.comparison2954
#print axioms sourceMap2954_checked
#print axioms fusedMap2954_checked
#print axioms certified2954
def sourceMap2954swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2954swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2954swap_checked : acceptsGraphIso
    (source (graph core2954) (root 10) 4 0) DegreeTwoThreeSpectrum6908.graph sourceMap2954swap=true := by decide +kernel
theorem fusedMap2954swap_checked : acceptsGraphIso
    (fused (graph core2954) (root 10) 4 0) DegreeTwoThreeSpectrum6909.graph fusedMap2954swap=true := by decide +kernel
theorem certified2954swap : Certified (graph core2954) (root 10) 4 0 :=
  of_native_maps core2954 DegreeTwoThreeSpectrum6908.graph DegreeTwoThreeSpectrum6909.graph
    sourceMap2954swap fusedMap2954swap sourceMap2954swap_checked fusedMap2954swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2954
#print axioms sourceMap2954swap_checked
#print axioms fusedMap2954swap_checked
#print axioms certified2954swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
