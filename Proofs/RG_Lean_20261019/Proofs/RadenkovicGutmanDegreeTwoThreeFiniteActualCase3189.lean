/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3189 : Family 8 := level8.get ⟨158,by decide⟩
def sourceMap3189 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3189 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3189_checked : acceptsGraphIso
    (source (graph core3189) (root 8) 0 5) DegreeTwoThreeSpectrum4527.graph sourceMap3189=true := by decide +kernel
theorem fusedMap3189_checked : acceptsGraphIso
    (fused (graph core3189) (root 8) 0 5) DegreeTwoThreeSpectrum4037.graph fusedMap3189=true := by decide +kernel
theorem certified3189 : Certified (graph core3189) (root 8) 0 5 :=
  of_native_maps core3189 DegreeTwoThreeSpectrum4527.graph DegreeTwoThreeSpectrum4037.graph
    sourceMap3189 fusedMap3189 sourceMap3189_checked fusedMap3189_checked
    DegreeTwoThreeFiniteComparisons.comparison3189
#print axioms sourceMap3189_checked
#print axioms fusedMap3189_checked
#print axioms certified3189
def sourceMap3189swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3189swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3189swap_checked : acceptsGraphIso
    (source (graph core3189) (root 8) 5 0) DegreeTwoThreeSpectrum4527.graph sourceMap3189swap=true := by decide +kernel
theorem fusedMap3189swap_checked : acceptsGraphIso
    (fused (graph core3189) (root 8) 5 0) DegreeTwoThreeSpectrum4037.graph fusedMap3189swap=true := by decide +kernel
theorem certified3189swap : Certified (graph core3189) (root 8) 5 0 :=
  of_native_maps core3189 DegreeTwoThreeSpectrum4527.graph DegreeTwoThreeSpectrum4037.graph
    sourceMap3189swap fusedMap3189swap sourceMap3189swap_checked fusedMap3189swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3189
#print axioms sourceMap3189swap_checked
#print axioms fusedMap3189swap_checked
#print axioms certified3189swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
