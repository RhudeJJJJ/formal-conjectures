/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2782 : Family 10 := level10.get ⟨1028,by decide⟩
def sourceMap2782 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2782 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2782_checked : acceptsGraphIso
    (source (graph core2782) (root 10) 0 4) DegreeTwoThreeSpectrum6037.graph sourceMap2782=true := by decide +kernel
theorem fusedMap2782_checked : acceptsGraphIso
    (fused (graph core2782) (root 10) 0 4) DegreeTwoThreeSpectrum6038.graph fusedMap2782=true := by decide +kernel
theorem certified2782 : Certified (graph core2782) (root 10) 0 4 :=
  of_native_maps core2782 DegreeTwoThreeSpectrum6037.graph DegreeTwoThreeSpectrum6038.graph
    sourceMap2782 fusedMap2782 sourceMap2782_checked fusedMap2782_checked
    DegreeTwoThreeFiniteComparisons.comparison2782
#print axioms sourceMap2782_checked
#print axioms fusedMap2782_checked
#print axioms certified2782
def sourceMap2782swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2782swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2782swap_checked : acceptsGraphIso
    (source (graph core2782) (root 10) 4 0) DegreeTwoThreeSpectrum6037.graph sourceMap2782swap=true := by decide +kernel
theorem fusedMap2782swap_checked : acceptsGraphIso
    (fused (graph core2782) (root 10) 4 0) DegreeTwoThreeSpectrum6038.graph fusedMap2782swap=true := by decide +kernel
theorem certified2782swap : Certified (graph core2782) (root 10) 4 0 :=
  of_native_maps core2782 DegreeTwoThreeSpectrum6037.graph DegreeTwoThreeSpectrum6038.graph
    sourceMap2782swap fusedMap2782swap sourceMap2782swap_checked fusedMap2782swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2782
#print axioms sourceMap2782swap_checked
#print axioms fusedMap2782swap_checked
#print axioms certified2782swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
