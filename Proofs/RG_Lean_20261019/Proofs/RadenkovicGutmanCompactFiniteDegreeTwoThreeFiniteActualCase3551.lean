/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3551 : Family 8 := level8.get ⟨56,by decide⟩
def sourceMap3551 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3551 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3551_checked : acceptsGraphIso
    (source (graph core3551) (root 8) 0 6) DegreeTwoThreeSpectrum5475.graph sourceMap3551=true := by decide +kernel
theorem fusedMap3551_checked : acceptsGraphIso
    (fused (graph core3551) (root 8) 0 6) DegreeTwoThreeSpectrum5011.graph fusedMap3551=true := by decide +kernel
theorem certified3551 : Certified (graph core3551) (root 8) 0 6 :=
  of_native_maps core3551 DegreeTwoThreeSpectrum5475.graph DegreeTwoThreeSpectrum5011.graph
    sourceMap3551 fusedMap3551 sourceMap3551_checked fusedMap3551_checked
    DegreeTwoThreeFiniteComparisons.comparison3551
#print axioms sourceMap3551_checked
#print axioms fusedMap3551_checked
#print axioms certified3551
def sourceMap3551swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3551swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3551swap_checked : acceptsGraphIso
    (source (graph core3551) (root 8) 6 0) DegreeTwoThreeSpectrum5475.graph sourceMap3551swap=true := by decide +kernel
theorem fusedMap3551swap_checked : acceptsGraphIso
    (fused (graph core3551) (root 8) 6 0) DegreeTwoThreeSpectrum5011.graph fusedMap3551swap=true := by decide +kernel
theorem certified3551swap : Certified (graph core3551) (root 8) 6 0 :=
  of_native_maps core3551 DegreeTwoThreeSpectrum5475.graph DegreeTwoThreeSpectrum5011.graph
    sourceMap3551swap fusedMap3551swap sourceMap3551swap_checked fusedMap3551swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3551
#print axioms sourceMap3551swap_checked
#print axioms fusedMap3551swap_checked
#print axioms certified3551swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
