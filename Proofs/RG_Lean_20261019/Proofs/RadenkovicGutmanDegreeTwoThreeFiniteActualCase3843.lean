/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3843 : Family 8 := level8.get ⟨68,by decide⟩
def sourceMap3843 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11] (sourceLabel 8 1 4 v)
def fusedMap3843 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3843_checked : acceptsGraphIso
    (source (graph core3843) (root 8) 1 4) DegreeTwoThreeSpectrum4538.graph sourceMap3843=true := by decide +kernel
theorem fusedMap3843_checked : acceptsGraphIso
    (fused (graph core3843) (root 8) 1 4) DegreeTwoThreeSpectrum4051.graph fusedMap3843=true := by decide +kernel
theorem certified3843 : Certified (graph core3843) (root 8) 1 4 :=
  of_native_maps core3843 DegreeTwoThreeSpectrum4538.graph DegreeTwoThreeSpectrum4051.graph
    sourceMap3843 fusedMap3843 sourceMap3843_checked fusedMap3843_checked
    DegreeTwoThreeFiniteComparisons.comparison3843
#print axioms sourceMap3843_checked
#print axioms fusedMap3843_checked
#print axioms certified3843
def sourceMap3843swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,7,8,9,10,11,14,15] (sourceLabel 8 4 1 v)
def fusedMap3843swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3843swap_checked : acceptsGraphIso
    (source (graph core3843) (root 8) 4 1) DegreeTwoThreeSpectrum4538.graph sourceMap3843swap=true := by decide +kernel
theorem fusedMap3843swap_checked : acceptsGraphIso
    (fused (graph core3843) (root 8) 4 1) DegreeTwoThreeSpectrum4051.graph fusedMap3843swap=true := by decide +kernel
theorem certified3843swap : Certified (graph core3843) (root 8) 4 1 :=
  of_native_maps core3843 DegreeTwoThreeSpectrum4538.graph DegreeTwoThreeSpectrum4051.graph
    sourceMap3843swap fusedMap3843swap sourceMap3843swap_checked fusedMap3843swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3843
#print axioms sourceMap3843swap_checked
#print axioms fusedMap3843swap_checked
#print axioms certified3843swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
