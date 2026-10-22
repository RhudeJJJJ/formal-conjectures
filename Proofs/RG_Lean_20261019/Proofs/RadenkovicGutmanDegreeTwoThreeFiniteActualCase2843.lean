/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2843 : Family 10 := level10.get ⟨1184,by decide⟩
def sourceMap2843 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2843 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2843_checked : acceptsGraphIso
    (source (graph core2843) (root 10) 0 4) DegreeTwoThreeSpectrum6352.graph sourceMap2843=true := by decide +kernel
theorem fusedMap2843_checked : acceptsGraphIso
    (fused (graph core2843) (root 10) 0 4) DegreeTwoThreeSpectrum6353.graph fusedMap2843=true := by decide +kernel
theorem certified2843 : Certified (graph core2843) (root 10) 0 4 :=
  of_native_maps core2843 DegreeTwoThreeSpectrum6352.graph DegreeTwoThreeSpectrum6353.graph
    sourceMap2843 fusedMap2843 sourceMap2843_checked fusedMap2843_checked
    DegreeTwoThreeFiniteComparisons.comparison2843
#print axioms sourceMap2843_checked
#print axioms fusedMap2843_checked
#print axioms certified2843
def sourceMap2843swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2843swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2843swap_checked : acceptsGraphIso
    (source (graph core2843) (root 10) 4 0) DegreeTwoThreeSpectrum6352.graph sourceMap2843swap=true := by decide +kernel
theorem fusedMap2843swap_checked : acceptsGraphIso
    (fused (graph core2843) (root 10) 4 0) DegreeTwoThreeSpectrum6353.graph fusedMap2843swap=true := by decide +kernel
theorem certified2843swap : Certified (graph core2843) (root 10) 4 0 :=
  of_native_maps core2843 DegreeTwoThreeSpectrum6352.graph DegreeTwoThreeSpectrum6353.graph
    sourceMap2843swap fusedMap2843swap sourceMap2843swap_checked fusedMap2843swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2843
#print axioms sourceMap2843swap_checked
#print axioms fusedMap2843swap_checked
#print axioms certified2843swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
