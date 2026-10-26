/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3840 : Family 8 := level8.get ⟨60,by decide⟩
def sourceMap3840 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3840 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3840_checked : acceptsGraphIso
    (source (graph core3840) (root 8) 1 4) DegreeTwoThreeSpectrum4480.graph sourceMap3840=true := by decide +kernel
theorem fusedMap3840_checked : acceptsGraphIso
    (fused (graph core3840) (root 8) 1 4) DegreeTwoThreeSpectrum4015.graph fusedMap3840=true := by decide +kernel
theorem certified3840 : Certified (graph core3840) (root 8) 1 4 :=
  of_native_maps core3840 DegreeTwoThreeSpectrum4480.graph DegreeTwoThreeSpectrum4015.graph
    sourceMap3840 fusedMap3840 sourceMap3840_checked fusedMap3840_checked
    DegreeTwoThreeFiniteComparisons.comparison3840
#print axioms sourceMap3840_checked
#print axioms fusedMap3840_checked
#print axioms certified3840
def sourceMap3840swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3840swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3840swap_checked : acceptsGraphIso
    (source (graph core3840) (root 8) 4 1) DegreeTwoThreeSpectrum4480.graph sourceMap3840swap=true := by decide +kernel
theorem fusedMap3840swap_checked : acceptsGraphIso
    (fused (graph core3840) (root 8) 4 1) DegreeTwoThreeSpectrum4015.graph fusedMap3840swap=true := by decide +kernel
theorem certified3840swap : Certified (graph core3840) (root 8) 4 1 :=
  of_native_maps core3840 DegreeTwoThreeSpectrum4480.graph DegreeTwoThreeSpectrum4015.graph
    sourceMap3840swap fusedMap3840swap sourceMap3840swap_checked fusedMap3840swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3840
#print axioms sourceMap3840swap_checked
#print axioms fusedMap3840swap_checked
#print axioms certified3840swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
