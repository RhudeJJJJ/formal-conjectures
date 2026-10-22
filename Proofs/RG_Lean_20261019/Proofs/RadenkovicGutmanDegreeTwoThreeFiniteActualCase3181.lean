/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3181 : Family 8 := level8.get ⟨139,by decide⟩
def sourceMap3181 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3181 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3181_checked : acceptsGraphIso
    (source (graph core3181) (root 8) 0 5) DegreeTwoThreeSpectrum4435.graph sourceMap3181=true := by decide +kernel
theorem fusedMap3181_checked : acceptsGraphIso
    (fused (graph core3181) (root 8) 0 5) DegreeTwoThreeSpectrum3992.graph fusedMap3181=true := by decide +kernel
theorem certified3181 : Certified (graph core3181) (root 8) 0 5 :=
  of_native_maps core3181 DegreeTwoThreeSpectrum4435.graph DegreeTwoThreeSpectrum3992.graph
    sourceMap3181 fusedMap3181 sourceMap3181_checked fusedMap3181_checked
    DegreeTwoThreeFiniteComparisons.comparison3181
#print axioms sourceMap3181_checked
#print axioms fusedMap3181_checked
#print axioms certified3181
def sourceMap3181swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3181swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3181swap_checked : acceptsGraphIso
    (source (graph core3181) (root 8) 5 0) DegreeTwoThreeSpectrum4435.graph sourceMap3181swap=true := by decide +kernel
theorem fusedMap3181swap_checked : acceptsGraphIso
    (fused (graph core3181) (root 8) 5 0) DegreeTwoThreeSpectrum3992.graph fusedMap3181swap=true := by decide +kernel
theorem certified3181swap : Certified (graph core3181) (root 8) 5 0 :=
  of_native_maps core3181 DegreeTwoThreeSpectrum4435.graph DegreeTwoThreeSpectrum3992.graph
    sourceMap3181swap fusedMap3181swap sourceMap3181swap_checked fusedMap3181swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3181
#print axioms sourceMap3181swap_checked
#print axioms fusedMap3181swap_checked
#print axioms certified3181swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
