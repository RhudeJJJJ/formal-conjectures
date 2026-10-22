/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2991 : Family 10 := level10.get ⟨1548,by decide⟩
def sourceMap2991 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2991 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2991_checked : acceptsGraphIso
    (source (graph core2991) (root 10) 0 4) DegreeTwoThreeSpectrum7086.graph sourceMap2991=true := by decide +kernel
theorem fusedMap2991_checked : acceptsGraphIso
    (fused (graph core2991) (root 10) 0 4) DegreeTwoThreeSpectrum5999.graph fusedMap2991=true := by decide +kernel
theorem certified2991 : Certified (graph core2991) (root 10) 0 4 :=
  of_native_maps core2991 DegreeTwoThreeSpectrum7086.graph DegreeTwoThreeSpectrum5999.graph
    sourceMap2991 fusedMap2991 sourceMap2991_checked fusedMap2991_checked
    DegreeTwoThreeFiniteComparisons.comparison2991
#print axioms sourceMap2991_checked
#print axioms fusedMap2991_checked
#print axioms certified2991
def sourceMap2991swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2991swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2991swap_checked : acceptsGraphIso
    (source (graph core2991) (root 10) 4 0) DegreeTwoThreeSpectrum7086.graph sourceMap2991swap=true := by decide +kernel
theorem fusedMap2991swap_checked : acceptsGraphIso
    (fused (graph core2991) (root 10) 4 0) DegreeTwoThreeSpectrum5999.graph fusedMap2991swap=true := by decide +kernel
theorem certified2991swap : Certified (graph core2991) (root 10) 4 0 :=
  of_native_maps core2991 DegreeTwoThreeSpectrum7086.graph DegreeTwoThreeSpectrum5999.graph
    sourceMap2991swap fusedMap2991swap sourceMap2991swap_checked fusedMap2991swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2991
#print axioms sourceMap2991swap_checked
#print axioms fusedMap2991swap_checked
#print axioms certified2991swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
