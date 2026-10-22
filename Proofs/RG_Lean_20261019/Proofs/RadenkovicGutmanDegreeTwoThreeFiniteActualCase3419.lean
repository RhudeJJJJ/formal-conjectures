/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3419 : Family 9 := level9.get ⟨535,by decide⟩
def sourceMap3419 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3419 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3419_checked : acceptsGraphIso
    (source (graph core3419) (root 9) 0 5) DegreeTwoThreeSpectrum7023.graph sourceMap3419=true := by decide +kernel
theorem fusedMap3419_checked : acceptsGraphIso
    (fused (graph core3419) (root 9) 0 5) DegreeTwoThreeSpectrum5839.graph fusedMap3419=true := by decide +kernel
theorem certified3419 : Certified (graph core3419) (root 9) 0 5 :=
  of_native_maps core3419 DegreeTwoThreeSpectrum7023.graph DegreeTwoThreeSpectrum5839.graph
    sourceMap3419 fusedMap3419 sourceMap3419_checked fusedMap3419_checked
    DegreeTwoThreeFiniteComparisons.comparison3419
#print axioms sourceMap3419_checked
#print axioms fusedMap3419_checked
#print axioms certified3419
def sourceMap3419swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3419swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3419swap_checked : acceptsGraphIso
    (source (graph core3419) (root 9) 5 0) DegreeTwoThreeSpectrum7023.graph sourceMap3419swap=true := by decide +kernel
theorem fusedMap3419swap_checked : acceptsGraphIso
    (fused (graph core3419) (root 9) 5 0) DegreeTwoThreeSpectrum5839.graph fusedMap3419swap=true := by decide +kernel
theorem certified3419swap : Certified (graph core3419) (root 9) 5 0 :=
  of_native_maps core3419 DegreeTwoThreeSpectrum7023.graph DegreeTwoThreeSpectrum5839.graph
    sourceMap3419swap fusedMap3419swap sourceMap3419swap_checked fusedMap3419swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3419
#print axioms sourceMap3419swap_checked
#print axioms fusedMap3419swap_checked
#print axioms certified3419swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
