/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3174 : Family 8 := level8.get ⟨123,by decide⟩
def sourceMap3174 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3174 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3174_checked : acceptsGraphIso
    (source (graph core3174) (root 8) 0 5) DegreeTwoThreeSpectrum4351.graph sourceMap3174=true := by decide +kernel
theorem fusedMap3174_checked : acceptsGraphIso
    (fused (graph core3174) (root 8) 0 5) DegreeTwoThreeSpectrum3944.graph fusedMap3174=true := by decide +kernel
theorem certified3174 : Certified (graph core3174) (root 8) 0 5 :=
  of_native_maps core3174 DegreeTwoThreeSpectrum4351.graph DegreeTwoThreeSpectrum3944.graph
    sourceMap3174 fusedMap3174 sourceMap3174_checked fusedMap3174_checked
    DegreeTwoThreeFiniteComparisons.comparison3174
#print axioms sourceMap3174_checked
#print axioms fusedMap3174_checked
#print axioms certified3174
def sourceMap3174swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3174swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3174swap_checked : acceptsGraphIso
    (source (graph core3174) (root 8) 5 0) DegreeTwoThreeSpectrum4351.graph sourceMap3174swap=true := by decide +kernel
theorem fusedMap3174swap_checked : acceptsGraphIso
    (fused (graph core3174) (root 8) 5 0) DegreeTwoThreeSpectrum3944.graph fusedMap3174swap=true := by decide +kernel
theorem certified3174swap : Certified (graph core3174) (root 8) 5 0 :=
  of_native_maps core3174 DegreeTwoThreeSpectrum4351.graph DegreeTwoThreeSpectrum3944.graph
    sourceMap3174swap fusedMap3174swap sourceMap3174swap_checked fusedMap3174swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3174
#print axioms sourceMap3174swap_checked
#print axioms fusedMap3174swap_checked
#print axioms certified3174swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
