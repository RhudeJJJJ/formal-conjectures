/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core045 : Family 6 := level6.get ⟨45,by decide⟩
def sourceMap045 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (sourceLabel 6 0 3 v)
def fusedMap045 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap045_checked : acceptsGraphIso
    (source (graph core045) (root 6) 0 3) SmallGeFourSpectrum169.graph
      sourceMap045=true := by decide +kernel
theorem fusedMap045_checked : acceptsGraphIso
    (fused (graph core045) (root 6) 0 3) SmallGeFourSpectrum099.graph
      fusedMap045=true := by decide +kernel
theorem certified045 : Certified (graph core045) (root 6) 0 3 :=
  of_native_maps core045 SmallGeFourSpectrum169.graph SmallGeFourSpectrum099.graph
    sourceMap045 fusedMap045 sourceMap045_checked fusedMap045_checked
    SmallGeFourComparisons.comparison045
#print axioms sourceMap045_checked
#print axioms fusedMap045_checked
#print axioms certified045
def sourceMap045swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,8] (sourceLabel 6 3 0 v)
def fusedMap045swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap045swap_checked : acceptsGraphIso
    (source (graph core045) (root 6) 3 0) SmallGeFourSpectrum169.graph
      sourceMap045swap=true := by decide +kernel
theorem fusedMap045swap_checked : acceptsGraphIso
    (fused (graph core045) (root 6) 3 0) SmallGeFourSpectrum099.graph
      fusedMap045swap=true := by decide +kernel
theorem certified045swap : Certified (graph core045) (root 6) 3 0 :=
  of_native_maps core045 SmallGeFourSpectrum169.graph SmallGeFourSpectrum099.graph
    sourceMap045swap fusedMap045swap sourceMap045swap_checked fusedMap045swap_checked
    SmallGeFourComparisons.comparison045
#print axioms sourceMap045swap_checked
#print axioms fusedMap045swap_checked
#print axioms certified045swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
