/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2987 : Family 10 := level10.get ⟨1538,by decide⟩
def sourceMap2987 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2987 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2987_checked : acceptsGraphIso
    (source (graph core2987) (root 10) 0 4) DegreeTwoThreeSpectrum7076.graph sourceMap2987=true := by decide +kernel
theorem fusedMap2987_checked : acceptsGraphIso
    (fused (graph core2987) (root 10) 0 4) DegreeTwoThreeSpectrum5982.graph fusedMap2987=true := by decide +kernel
theorem certified2987 : Certified (graph core2987) (root 10) 0 4 :=
  of_native_maps core2987 DegreeTwoThreeSpectrum7076.graph DegreeTwoThreeSpectrum5982.graph
    sourceMap2987 fusedMap2987 sourceMap2987_checked fusedMap2987_checked
    DegreeTwoThreeFiniteComparisons.comparison2987
#print axioms sourceMap2987_checked
#print axioms fusedMap2987_checked
#print axioms certified2987
def sourceMap2987swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2987swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2987swap_checked : acceptsGraphIso
    (source (graph core2987) (root 10) 4 0) DegreeTwoThreeSpectrum7076.graph sourceMap2987swap=true := by decide +kernel
theorem fusedMap2987swap_checked : acceptsGraphIso
    (fused (graph core2987) (root 10) 4 0) DegreeTwoThreeSpectrum5982.graph fusedMap2987swap=true := by decide +kernel
theorem certified2987swap : Certified (graph core2987) (root 10) 4 0 :=
  of_native_maps core2987 DegreeTwoThreeSpectrum7076.graph DegreeTwoThreeSpectrum5982.graph
    sourceMap2987swap fusedMap2987swap sourceMap2987swap_checked fusedMap2987swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2987
#print axioms sourceMap2987swap_checked
#print axioms fusedMap2987swap_checked
#print axioms certified2987swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
