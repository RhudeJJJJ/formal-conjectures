/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core101 : Family 7 := level7.get ⟨113,by decide⟩
def sourceMap101 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,5,6,7,8,9,10,3,4] (sourceLabel 7 0 1 v)
def fusedMap101 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap101_checked : acceptsGraphIso
    (source (graph core101) (root 7) 0 1) SmallGeFourSpectrum091.graph
      sourceMap101=true := by decide +kernel
theorem fusedMap101_checked : acceptsGraphIso
    (fused (graph core101) (root 7) 0 1) SmallGeFourSpectrum060.graph
      fusedMap101=true := by decide +kernel
theorem certified101 : Certified (graph core101) (root 7) 0 1 :=
  of_native_maps core101 SmallGeFourSpectrum091.graph SmallGeFourSpectrum060.graph
    sourceMap101 fusedMap101 sourceMap101_checked fusedMap101_checked
    SmallGeFourComparisons.comparison101
#print axioms sourceMap101_checked
#print axioms fusedMap101_checked
#print axioms certified101
def sourceMap101swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,5,6,7,8,9,3,4,10] (sourceLabel 7 1 0 v)
def fusedMap101swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap101swap_checked : acceptsGraphIso
    (source (graph core101) (root 7) 1 0) SmallGeFourSpectrum091.graph
      sourceMap101swap=true := by decide +kernel
theorem fusedMap101swap_checked : acceptsGraphIso
    (fused (graph core101) (root 7) 1 0) SmallGeFourSpectrum060.graph
      fusedMap101swap=true := by decide +kernel
theorem certified101swap : Certified (graph core101) (root 7) 1 0 :=
  of_native_maps core101 SmallGeFourSpectrum091.graph SmallGeFourSpectrum060.graph
    sourceMap101swap fusedMap101swap sourceMap101swap_checked fusedMap101swap_checked
    SmallGeFourComparisons.comparison101
#print axioms sourceMap101swap_checked
#print axioms fusedMap101swap_checked
#print axioms certified101swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
