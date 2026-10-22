/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3941 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap3941 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3941 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3941_checked : acceptsGraphIso
    (source (graph core3941) (root 6) 1 5) DegreeTwoThreeSpectrum2570.graph sourceMap3941=true := by decide +kernel
theorem fusedMap3941_checked : acceptsGraphIso
    (fused (graph core3941) (root 6) 1 5) DegreeTwoThreeSpectrum2328.graph fusedMap3941=true := by decide +kernel
theorem certified3941 : Certified (graph core3941) (root 6) 1 5 :=
  of_native_maps core3941 DegreeTwoThreeSpectrum2570.graph DegreeTwoThreeSpectrum2328.graph
    sourceMap3941 fusedMap3941 sourceMap3941_checked fusedMap3941_checked
    DegreeTwoThreeFiniteComparisons.comparison3941
#print axioms sourceMap3941_checked
#print axioms fusedMap3941_checked
#print axioms certified3941
def sourceMap3941swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,10,11,12,13,14,8,9] (sourceLabel 6 5 1 v)
def fusedMap3941swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3941swap_checked : acceptsGraphIso
    (source (graph core3941) (root 6) 5 1) DegreeTwoThreeSpectrum2570.graph sourceMap3941swap=true := by decide +kernel
theorem fusedMap3941swap_checked : acceptsGraphIso
    (fused (graph core3941) (root 6) 5 1) DegreeTwoThreeSpectrum2328.graph fusedMap3941swap=true := by decide +kernel
theorem certified3941swap : Certified (graph core3941) (root 6) 5 1 :=
  of_native_maps core3941 DegreeTwoThreeSpectrum2570.graph DegreeTwoThreeSpectrum2328.graph
    sourceMap3941swap fusedMap3941swap sourceMap3941swap_checked fusedMap3941swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3941
#print axioms sourceMap3941swap_checked
#print axioms fusedMap3941swap_checked
#print axioms certified3941swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
