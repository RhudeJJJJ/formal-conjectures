/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3179 : Family 8 := level8.get ⟨135,by decide⟩
def sourceMap3179 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3179 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3179_checked : acceptsGraphIso
    (source (graph core3179) (root 8) 0 5) DegreeTwoThreeSpectrum4412.graph sourceMap3179=true := by decide +kernel
theorem fusedMap3179_checked : acceptsGraphIso
    (fused (graph core3179) (root 8) 0 5) DegreeTwoThreeSpectrum3984.graph fusedMap3179=true := by decide +kernel
theorem certified3179 : Certified (graph core3179) (root 8) 0 5 :=
  of_native_maps core3179 DegreeTwoThreeSpectrum4412.graph DegreeTwoThreeSpectrum3984.graph
    sourceMap3179 fusedMap3179 sourceMap3179_checked fusedMap3179_checked
    DegreeTwoThreeFiniteComparisons.comparison3179
#print axioms sourceMap3179_checked
#print axioms fusedMap3179_checked
#print axioms certified3179
def sourceMap3179swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3179swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3179swap_checked : acceptsGraphIso
    (source (graph core3179) (root 8) 5 0) DegreeTwoThreeSpectrum4412.graph sourceMap3179swap=true := by decide +kernel
theorem fusedMap3179swap_checked : acceptsGraphIso
    (fused (graph core3179) (root 8) 5 0) DegreeTwoThreeSpectrum3984.graph fusedMap3179swap=true := by decide +kernel
theorem certified3179swap : Certified (graph core3179) (root 8) 5 0 :=
  of_native_maps core3179 DegreeTwoThreeSpectrum4412.graph DegreeTwoThreeSpectrum3984.graph
    sourceMap3179swap fusedMap3179swap sourceMap3179swap_checked fusedMap3179swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3179
#print axioms sourceMap3179swap_checked
#print axioms fusedMap3179swap_checked
#print axioms certified3179swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
