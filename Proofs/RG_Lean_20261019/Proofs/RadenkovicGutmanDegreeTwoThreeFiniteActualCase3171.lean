/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3171 : Family 8 := level8.get ⟨114,by decide⟩
def sourceMap3171 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3171 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3171_checked : acceptsGraphIso
    (source (graph core3171) (root 8) 0 5) DegreeTwoThreeSpectrum4301.graph sourceMap3171=true := by decide +kernel
theorem fusedMap3171_checked : acceptsGraphIso
    (fused (graph core3171) (root 8) 0 5) DegreeTwoThreeSpectrum3924.graph fusedMap3171=true := by decide +kernel
theorem certified3171 : Certified (graph core3171) (root 8) 0 5 :=
  of_native_maps core3171 DegreeTwoThreeSpectrum4301.graph DegreeTwoThreeSpectrum3924.graph
    sourceMap3171 fusedMap3171 sourceMap3171_checked fusedMap3171_checked
    DegreeTwoThreeFiniteComparisons.comparison3171
#print axioms sourceMap3171_checked
#print axioms fusedMap3171_checked
#print axioms certified3171
def sourceMap3171swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3171swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3171swap_checked : acceptsGraphIso
    (source (graph core3171) (root 8) 5 0) DegreeTwoThreeSpectrum4301.graph sourceMap3171swap=true := by decide +kernel
theorem fusedMap3171swap_checked : acceptsGraphIso
    (fused (graph core3171) (root 8) 5 0) DegreeTwoThreeSpectrum3924.graph fusedMap3171swap=true := by decide +kernel
theorem certified3171swap : Certified (graph core3171) (root 8) 5 0 :=
  of_native_maps core3171 DegreeTwoThreeSpectrum4301.graph DegreeTwoThreeSpectrum3924.graph
    sourceMap3171swap fusedMap3171swap sourceMap3171swap_checked fusedMap3171swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3171
#print axioms sourceMap3171swap_checked
#print axioms fusedMap3171swap_checked
#print axioms certified3171swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
