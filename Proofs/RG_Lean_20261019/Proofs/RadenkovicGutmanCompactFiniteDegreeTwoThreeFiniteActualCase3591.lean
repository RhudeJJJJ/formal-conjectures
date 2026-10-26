/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3591 : Family 8 := level8.get ⟨168,by decide⟩
def sourceMap3591 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3591 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3591_checked : acceptsGraphIso
    (source (graph core3591) (root 8) 0 6) DegreeTwoThreeSpectrum5695.graph sourceMap3591=true := by decide +kernel
theorem fusedMap3591_checked : acceptsGraphIso
    (fused (graph core3591) (root 8) 0 6) DegreeTwoThreeSpectrum5697.graph fusedMap3591=true := by decide +kernel
theorem certified3591 : Certified (graph core3591) (root 8) 0 6 :=
  of_native_maps core3591 DegreeTwoThreeSpectrum5695.graph DegreeTwoThreeSpectrum5697.graph
    sourceMap3591 fusedMap3591 sourceMap3591_checked fusedMap3591_checked
    DegreeTwoThreeFiniteComparisons.comparison3591
#print axioms sourceMap3591_checked
#print axioms fusedMap3591_checked
#print axioms certified3591
def sourceMap3591swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3591swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3591swap_checked : acceptsGraphIso
    (source (graph core3591) (root 8) 6 0) DegreeTwoThreeSpectrum5695.graph sourceMap3591swap=true := by decide +kernel
theorem fusedMap3591swap_checked : acceptsGraphIso
    (fused (graph core3591) (root 8) 6 0) DegreeTwoThreeSpectrum5697.graph fusedMap3591swap=true := by decide +kernel
theorem certified3591swap : Certified (graph core3591) (root 8) 6 0 :=
  of_native_maps core3591 DegreeTwoThreeSpectrum5695.graph DegreeTwoThreeSpectrum5697.graph
    sourceMap3591swap fusedMap3591swap sourceMap3591swap_checked fusedMap3591swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3591
#print axioms sourceMap3591swap_checked
#print axioms fusedMap3591swap_checked
#print axioms certified3591swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
