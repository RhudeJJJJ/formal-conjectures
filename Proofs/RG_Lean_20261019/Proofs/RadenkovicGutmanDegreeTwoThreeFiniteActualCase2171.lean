/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2171 : Family 8 := level8.get ⟨168,by decide⟩
def sourceMap2171 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2171 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2171_checked : acceptsGraphIso
    (source (graph core2171) (root 8) 0 4) DegreeTwoThreeSpectrum2845.graph sourceMap2171=true := by decide +kernel
theorem fusedMap2171_checked : acceptsGraphIso
    (fused (graph core2171) (root 8) 0 4) DegreeTwoThreeSpectrum2848.graph fusedMap2171=true := by decide +kernel
theorem certified2171 : Certified (graph core2171) (root 8) 0 4 :=
  of_native_maps core2171 DegreeTwoThreeSpectrum2845.graph DegreeTwoThreeSpectrum2848.graph
    sourceMap2171 fusedMap2171 sourceMap2171_checked fusedMap2171_checked
    DegreeTwoThreeFiniteComparisons.comparison2171
#print axioms sourceMap2171_checked
#print axioms fusedMap2171_checked
#print axioms certified2171
def sourceMap2171swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2171swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2171swap_checked : acceptsGraphIso
    (source (graph core2171) (root 8) 4 0) DegreeTwoThreeSpectrum2845.graph sourceMap2171swap=true := by decide +kernel
theorem fusedMap2171swap_checked : acceptsGraphIso
    (fused (graph core2171) (root 8) 4 0) DegreeTwoThreeSpectrum2848.graph fusedMap2171swap=true := by decide +kernel
theorem certified2171swap : Certified (graph core2171) (root 8) 4 0 :=
  of_native_maps core2171 DegreeTwoThreeSpectrum2845.graph DegreeTwoThreeSpectrum2848.graph
    sourceMap2171swap fusedMap2171swap sourceMap2171swap_checked fusedMap2171swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2171
#print axioms sourceMap2171swap_checked
#print axioms fusedMap2171swap_checked
#print axioms certified2171swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
