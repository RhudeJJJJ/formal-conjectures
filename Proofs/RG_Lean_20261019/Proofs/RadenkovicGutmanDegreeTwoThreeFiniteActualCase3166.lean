/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3166 : Family 8 := level8.get ⟨98,by decide⟩
def sourceMap3166 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3166 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3166_checked : acceptsGraphIso
    (source (graph core3166) (root 8) 0 5) DegreeTwoThreeSpectrum4202.graph sourceMap3166=true := by decide +kernel
theorem fusedMap3166_checked : acceptsGraphIso
    (fused (graph core3166) (root 8) 0 5) DegreeTwoThreeSpectrum3895.graph fusedMap3166=true := by decide +kernel
theorem certified3166 : Certified (graph core3166) (root 8) 0 5 :=
  of_native_maps core3166 DegreeTwoThreeSpectrum4202.graph DegreeTwoThreeSpectrum3895.graph
    sourceMap3166 fusedMap3166 sourceMap3166_checked fusedMap3166_checked
    DegreeTwoThreeFiniteComparisons.comparison3166
#print axioms sourceMap3166_checked
#print axioms fusedMap3166_checked
#print axioms certified3166
def sourceMap3166swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3166swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3166swap_checked : acceptsGraphIso
    (source (graph core3166) (root 8) 5 0) DegreeTwoThreeSpectrum4202.graph sourceMap3166swap=true := by decide +kernel
theorem fusedMap3166swap_checked : acceptsGraphIso
    (fused (graph core3166) (root 8) 5 0) DegreeTwoThreeSpectrum3895.graph fusedMap3166swap=true := by decide +kernel
theorem certified3166swap : Certified (graph core3166) (root 8) 5 0 :=
  of_native_maps core3166 DegreeTwoThreeSpectrum4202.graph DegreeTwoThreeSpectrum3895.graph
    sourceMap3166swap fusedMap3166swap sourceMap3166swap_checked fusedMap3166swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3166
#print axioms sourceMap3166swap_checked
#print axioms fusedMap3166swap_checked
#print axioms certified3166swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
