/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3185 : Family 8 := level8.get ⟨152,by decide⟩
def sourceMap3185 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3185 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3185_checked : acceptsGraphIso
    (source (graph core3185) (root 8) 0 5) DegreeTwoThreeSpectrum4499.graph sourceMap3185=true := by decide +kernel
theorem fusedMap3185_checked : acceptsGraphIso
    (fused (graph core3185) (root 8) 0 5) DegreeTwoThreeSpectrum4021.graph fusedMap3185=true := by decide +kernel
theorem certified3185 : Certified (graph core3185) (root 8) 0 5 :=
  of_native_maps core3185 DegreeTwoThreeSpectrum4499.graph DegreeTwoThreeSpectrum4021.graph
    sourceMap3185 fusedMap3185 sourceMap3185_checked fusedMap3185_checked
    DegreeTwoThreeFiniteComparisons.comparison3185
#print axioms sourceMap3185_checked
#print axioms fusedMap3185_checked
#print axioms certified3185
def sourceMap3185swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3185swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3185swap_checked : acceptsGraphIso
    (source (graph core3185) (root 8) 5 0) DegreeTwoThreeSpectrum4499.graph sourceMap3185swap=true := by decide +kernel
theorem fusedMap3185swap_checked : acceptsGraphIso
    (fused (graph core3185) (root 8) 5 0) DegreeTwoThreeSpectrum4021.graph fusedMap3185swap=true := by decide +kernel
theorem certified3185swap : Certified (graph core3185) (root 8) 5 0 :=
  of_native_maps core3185 DegreeTwoThreeSpectrum4499.graph DegreeTwoThreeSpectrum4021.graph
    sourceMap3185swap fusedMap3185swap sourceMap3185swap_checked fusedMap3185swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3185
#print axioms sourceMap3185swap_checked
#print axioms fusedMap3185swap_checked
#print axioms certified3185swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
