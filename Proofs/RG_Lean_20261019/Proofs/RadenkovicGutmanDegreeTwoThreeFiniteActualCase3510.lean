/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3510 : Family 7 := level7.get ⟨36,by decide⟩
def sourceMap3510 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3510 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3510_checked : acceptsGraphIso
    (source (graph core3510) (root 7) 0 6) DegreeTwoThreeSpectrum3951.graph sourceMap3510=true := by decide +kernel
theorem fusedMap3510_checked : acceptsGraphIso
    (fused (graph core3510) (root 7) 0 6) DegreeTwoThreeSpectrum3953.graph fusedMap3510=true := by decide +kernel
theorem certified3510 : Certified (graph core3510) (root 7) 0 6 :=
  of_native_maps core3510 DegreeTwoThreeSpectrum3951.graph DegreeTwoThreeSpectrum3953.graph
    sourceMap3510 fusedMap3510 sourceMap3510_checked fusedMap3510_checked
    DegreeTwoThreeFiniteComparisons.comparison3510
#print axioms sourceMap3510_checked
#print axioms fusedMap3510_checked
#print axioms certified3510
def sourceMap3510swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3510swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3510swap_checked : acceptsGraphIso
    (source (graph core3510) (root 7) 6 0) DegreeTwoThreeSpectrum3951.graph sourceMap3510swap=true := by decide +kernel
theorem fusedMap3510swap_checked : acceptsGraphIso
    (fused (graph core3510) (root 7) 6 0) DegreeTwoThreeSpectrum3953.graph fusedMap3510swap=true := by decide +kernel
theorem certified3510swap : Certified (graph core3510) (root 7) 6 0 :=
  of_native_maps core3510 DegreeTwoThreeSpectrum3951.graph DegreeTwoThreeSpectrum3953.graph
    sourceMap3510swap fusedMap3510swap sourceMap3510swap_checked fusedMap3510swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3510
#print axioms sourceMap3510swap_checked
#print axioms fusedMap3510swap_checked
#print axioms certified3510swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
