/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2992 : Family 10 := level10.get ⟨1551,by decide⟩
def sourceMap2992 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2992 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2992_checked : acceptsGraphIso
    (source (graph core2992) (root 10) 0 4) DegreeTwoThreeSpectrum7088.graph sourceMap2992=true := by decide +kernel
theorem fusedMap2992_checked : acceptsGraphIso
    (fused (graph core2992) (root 10) 0 4) DegreeTwoThreeSpectrum6004.graph fusedMap2992=true := by decide +kernel
theorem certified2992 : Certified (graph core2992) (root 10) 0 4 :=
  of_native_maps core2992 DegreeTwoThreeSpectrum7088.graph DegreeTwoThreeSpectrum6004.graph
    sourceMap2992 fusedMap2992 sourceMap2992_checked fusedMap2992_checked
    DegreeTwoThreeFiniteComparisons.comparison2992
#print axioms sourceMap2992_checked
#print axioms fusedMap2992_checked
#print axioms certified2992
def sourceMap2992swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2992swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2992swap_checked : acceptsGraphIso
    (source (graph core2992) (root 10) 4 0) DegreeTwoThreeSpectrum7088.graph sourceMap2992swap=true := by decide +kernel
theorem fusedMap2992swap_checked : acceptsGraphIso
    (fused (graph core2992) (root 10) 4 0) DegreeTwoThreeSpectrum6004.graph fusedMap2992swap=true := by decide +kernel
theorem certified2992swap : Certified (graph core2992) (root 10) 4 0 :=
  of_native_maps core2992 DegreeTwoThreeSpectrum7088.graph DegreeTwoThreeSpectrum6004.graph
    sourceMap2992swap fusedMap2992swap sourceMap2992swap_checked fusedMap2992swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2992
#print axioms sourceMap2992swap_checked
#print axioms fusedMap2992swap_checked
#print axioms certified2992swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
