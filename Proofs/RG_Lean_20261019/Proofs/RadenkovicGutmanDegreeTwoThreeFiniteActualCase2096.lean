/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2096 : Family 7 := level7.get ⟨53,by decide⟩
def sourceMap2096 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2096 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2096_checked : acceptsGraphIso
    (source (graph core2096) (root 7) 0 4) DegreeTwoThreeSpectrum1871.graph sourceMap2096=true := by decide +kernel
theorem fusedMap2096_checked : acceptsGraphIso
    (fused (graph core2096) (root 7) 0 4) DegreeTwoThreeSpectrum1873.graph fusedMap2096=true := by decide +kernel
theorem certified2096 : Certified (graph core2096) (root 7) 0 4 :=
  of_native_maps core2096 DegreeTwoThreeSpectrum1871.graph DegreeTwoThreeSpectrum1873.graph
    sourceMap2096 fusedMap2096 sourceMap2096_checked fusedMap2096_checked
    DegreeTwoThreeFiniteComparisons.comparison2096
#print axioms sourceMap2096_checked
#print axioms fusedMap2096_checked
#print axioms certified2096
def sourceMap2096swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,8] (sourceLabel 7 4 0 v)
def fusedMap2096swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2096swap_checked : acceptsGraphIso
    (source (graph core2096) (root 7) 4 0) DegreeTwoThreeSpectrum1871.graph sourceMap2096swap=true := by decide +kernel
theorem fusedMap2096swap_checked : acceptsGraphIso
    (fused (graph core2096) (root 7) 4 0) DegreeTwoThreeSpectrum1873.graph fusedMap2096swap=true := by decide +kernel
theorem certified2096swap : Certified (graph core2096) (root 7) 4 0 :=
  of_native_maps core2096 DegreeTwoThreeSpectrum1871.graph DegreeTwoThreeSpectrum1873.graph
    sourceMap2096swap fusedMap2096swap sourceMap2096swap_checked fusedMap2096swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2096
#print axioms sourceMap2096swap_checked
#print axioms fusedMap2096swap_checked
#print axioms certified2096swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
