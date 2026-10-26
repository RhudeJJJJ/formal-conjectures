/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3848 : Family 8 := level8.get ⟨86,by decide⟩
def sourceMap3848 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3848 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3848_checked : acceptsGraphIso
    (source (graph core3848) (root 8) 1 4) DegreeTwoThreeSpectrum4652.graph sourceMap3848=true := by decide +kernel
theorem fusedMap3848_checked : acceptsGraphIso
    (fused (graph core3848) (root 8) 1 4) DegreeTwoThreeSpectrum4130.graph fusedMap3848=true := by decide +kernel
theorem certified3848 : Certified (graph core3848) (root 8) 1 4 :=
  of_native_maps core3848 DegreeTwoThreeSpectrum4652.graph DegreeTwoThreeSpectrum4130.graph
    sourceMap3848 fusedMap3848 sourceMap3848_checked fusedMap3848_checked
    DegreeTwoThreeFiniteComparisons.comparison3848
#print axioms sourceMap3848_checked
#print axioms fusedMap3848_checked
#print axioms certified3848
def sourceMap3848swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3848swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3848swap_checked : acceptsGraphIso
    (source (graph core3848) (root 8) 4 1) DegreeTwoThreeSpectrum4652.graph sourceMap3848swap=true := by decide +kernel
theorem fusedMap3848swap_checked : acceptsGraphIso
    (fused (graph core3848) (root 8) 4 1) DegreeTwoThreeSpectrum4130.graph fusedMap3848swap=true := by decide +kernel
theorem certified3848swap : Certified (graph core3848) (root 8) 4 1 :=
  of_native_maps core3848 DegreeTwoThreeSpectrum4652.graph DegreeTwoThreeSpectrum4130.graph
    sourceMap3848swap fusedMap3848swap sourceMap3848swap_checked fusedMap3848swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3848
#print axioms sourceMap3848swap_checked
#print axioms fusedMap3848swap_checked
#print axioms certified3848swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
