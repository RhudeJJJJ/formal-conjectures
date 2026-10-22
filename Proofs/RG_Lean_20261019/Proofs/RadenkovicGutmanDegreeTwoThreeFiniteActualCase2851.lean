/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2851 : Family 10 := level10.get ⟨1201,by decide⟩
def sourceMap2851 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2851 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2851_checked : acceptsGraphIso
    (source (graph core2851) (root 10) 0 4) DegreeTwoThreeSpectrum6378.graph sourceMap2851=true := by decide +kernel
theorem fusedMap2851_checked : acceptsGraphIso
    (fused (graph core2851) (root 10) 0 4) DegreeTwoThreeSpectrum6379.graph fusedMap2851=true := by decide +kernel
theorem certified2851 : Certified (graph core2851) (root 10) 0 4 :=
  of_native_maps core2851 DegreeTwoThreeSpectrum6378.graph DegreeTwoThreeSpectrum6379.graph
    sourceMap2851 fusedMap2851 sourceMap2851_checked fusedMap2851_checked
    DegreeTwoThreeFiniteComparisons.comparison2851
#print axioms sourceMap2851_checked
#print axioms fusedMap2851_checked
#print axioms certified2851
def sourceMap2851swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2851swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2851swap_checked : acceptsGraphIso
    (source (graph core2851) (root 10) 4 0) DegreeTwoThreeSpectrum6378.graph sourceMap2851swap=true := by decide +kernel
theorem fusedMap2851swap_checked : acceptsGraphIso
    (fused (graph core2851) (root 10) 4 0) DegreeTwoThreeSpectrum6379.graph fusedMap2851swap=true := by decide +kernel
theorem certified2851swap : Certified (graph core2851) (root 10) 4 0 :=
  of_native_maps core2851 DegreeTwoThreeSpectrum6378.graph DegreeTwoThreeSpectrum6379.graph
    sourceMap2851swap fusedMap2851swap sourceMap2851swap_checked fusedMap2851swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2851
#print axioms sourceMap2851swap_checked
#print axioms fusedMap2851swap_checked
#print axioms certified2851swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
