/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2857 : Family 10 := level10.get ⟨1213,by decide⟩
def sourceMap2857 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2857 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2857_checked : acceptsGraphIso
    (source (graph core2857) (root 10) 0 4) DegreeTwoThreeSpectrum6400.graph sourceMap2857=true := by decide +kernel
theorem fusedMap2857_checked : acceptsGraphIso
    (fused (graph core2857) (root 10) 0 4) DegreeTwoThreeSpectrum6401.graph fusedMap2857=true := by decide +kernel
theorem certified2857 : Certified (graph core2857) (root 10) 0 4 :=
  of_native_maps core2857 DegreeTwoThreeSpectrum6400.graph DegreeTwoThreeSpectrum6401.graph
    sourceMap2857 fusedMap2857 sourceMap2857_checked fusedMap2857_checked
    DegreeTwoThreeFiniteComparisons.comparison2857
#print axioms sourceMap2857_checked
#print axioms fusedMap2857_checked
#print axioms certified2857
def sourceMap2857swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2857swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2857swap_checked : acceptsGraphIso
    (source (graph core2857) (root 10) 4 0) DegreeTwoThreeSpectrum6400.graph sourceMap2857swap=true := by decide +kernel
theorem fusedMap2857swap_checked : acceptsGraphIso
    (fused (graph core2857) (root 10) 4 0) DegreeTwoThreeSpectrum6401.graph fusedMap2857swap=true := by decide +kernel
theorem certified2857swap : Certified (graph core2857) (root 10) 4 0 :=
  of_native_maps core2857 DegreeTwoThreeSpectrum6400.graph DegreeTwoThreeSpectrum6401.graph
    sourceMap2857swap fusedMap2857swap sourceMap2857swap_checked fusedMap2857swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2857
#print axioms sourceMap2857swap_checked
#print axioms fusedMap2857swap_checked
#print axioms certified2857swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
