/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2965 : Family 10 := level10.get ⟨1467,by decide⟩
def sourceMap2965 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2965 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2965_checked : acceptsGraphIso
    (source (graph core2965) (root 10) 0 4) DegreeTwoThreeSpectrum6946.graph sourceMap2965=true := by decide +kernel
theorem fusedMap2965_checked : acceptsGraphIso
    (fused (graph core2965) (root 10) 0 4) DegreeTwoThreeSpectrum6947.graph fusedMap2965=true := by decide +kernel
theorem certified2965 : Certified (graph core2965) (root 10) 0 4 :=
  of_native_maps core2965 DegreeTwoThreeSpectrum6946.graph DegreeTwoThreeSpectrum6947.graph
    sourceMap2965 fusedMap2965 sourceMap2965_checked fusedMap2965_checked
    DegreeTwoThreeFiniteComparisons.comparison2965
#print axioms sourceMap2965_checked
#print axioms fusedMap2965_checked
#print axioms certified2965
def sourceMap2965swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2965swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2965swap_checked : acceptsGraphIso
    (source (graph core2965) (root 10) 4 0) DegreeTwoThreeSpectrum6946.graph sourceMap2965swap=true := by decide +kernel
theorem fusedMap2965swap_checked : acceptsGraphIso
    (fused (graph core2965) (root 10) 4 0) DegreeTwoThreeSpectrum6947.graph fusedMap2965swap=true := by decide +kernel
theorem certified2965swap : Certified (graph core2965) (root 10) 4 0 :=
  of_native_maps core2965 DegreeTwoThreeSpectrum6946.graph DegreeTwoThreeSpectrum6947.graph
    sourceMap2965swap fusedMap2965swap sourceMap2965swap_checked fusedMap2965swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2965
#print axioms sourceMap2965swap_checked
#print axioms fusedMap2965swap_checked
#print axioms certified2965swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
