/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3634 : Family 8 := level8.get ⟨271,by decide⟩
def sourceMap3634 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3634 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3634_checked : acceptsGraphIso
    (source (graph core3634) (root 8) 0 6) DegreeTwoThreeSpectrum6045.graph sourceMap3634=true := by decide +kernel
theorem fusedMap3634_checked : acceptsGraphIso
    (fused (graph core3634) (root 8) 0 6) DegreeTwoThreeSpectrum6047.graph fusedMap3634=true := by decide +kernel
theorem certified3634 : Certified (graph core3634) (root 8) 0 6 :=
  of_native_maps core3634 DegreeTwoThreeSpectrum6045.graph DegreeTwoThreeSpectrum6047.graph
    sourceMap3634 fusedMap3634 sourceMap3634_checked fusedMap3634_checked
    DegreeTwoThreeFiniteComparisons.comparison3634
#print axioms sourceMap3634_checked
#print axioms fusedMap3634_checked
#print axioms certified3634
def sourceMap3634swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3634swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3634swap_checked : acceptsGraphIso
    (source (graph core3634) (root 8) 6 0) DegreeTwoThreeSpectrum6045.graph sourceMap3634swap=true := by decide +kernel
theorem fusedMap3634swap_checked : acceptsGraphIso
    (fused (graph core3634) (root 8) 6 0) DegreeTwoThreeSpectrum6047.graph fusedMap3634swap=true := by decide +kernel
theorem certified3634swap : Certified (graph core3634) (root 8) 6 0 :=
  of_native_maps core3634 DegreeTwoThreeSpectrum6045.graph DegreeTwoThreeSpectrum6047.graph
    sourceMap3634swap fusedMap3634swap sourceMap3634swap_checked fusedMap3634swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3634
#print axioms sourceMap3634swap_checked
#print axioms fusedMap3634swap_checked
#print axioms certified3634swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
