/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2990 : Family 10 := level10.get ⟨1547,by decide⟩
def sourceMap2990 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2990 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2990_checked : acceptsGraphIso
    (source (graph core2990) (root 10) 0 4) DegreeTwoThreeSpectrum7085.graph sourceMap2990=true := by decide +kernel
theorem fusedMap2990_checked : acceptsGraphIso
    (fused (graph core2990) (root 10) 0 4) DegreeTwoThreeSpectrum5997.graph fusedMap2990=true := by decide +kernel
theorem certified2990 : Certified (graph core2990) (root 10) 0 4 :=
  of_native_maps core2990 DegreeTwoThreeSpectrum7085.graph DegreeTwoThreeSpectrum5997.graph
    sourceMap2990 fusedMap2990 sourceMap2990_checked fusedMap2990_checked
    DegreeTwoThreeFiniteComparisons.comparison2990
#print axioms sourceMap2990_checked
#print axioms fusedMap2990_checked
#print axioms certified2990
def sourceMap2990swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2990swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2990swap_checked : acceptsGraphIso
    (source (graph core2990) (root 10) 4 0) DegreeTwoThreeSpectrum7085.graph sourceMap2990swap=true := by decide +kernel
theorem fusedMap2990swap_checked : acceptsGraphIso
    (fused (graph core2990) (root 10) 4 0) DegreeTwoThreeSpectrum5997.graph fusedMap2990swap=true := by decide +kernel
theorem certified2990swap : Certified (graph core2990) (root 10) 4 0 :=
  of_native_maps core2990 DegreeTwoThreeSpectrum7085.graph DegreeTwoThreeSpectrum5997.graph
    sourceMap2990swap fusedMap2990swap sourceMap2990swap_checked fusedMap2990swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2990
#print axioms sourceMap2990swap_checked
#print axioms fusedMap2990swap_checked
#print axioms certified2990swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
