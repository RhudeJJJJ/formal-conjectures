/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core115 : Family 8 := level8.get ⟨178,by decide⟩
def sourceMap115 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (sourceLabel 8 0 1 v)
def fusedMap115 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,4,5,6,1,2,3] (fusedLabel 8 0 1 v)
theorem sourceMap115_checked : acceptsGraphIso
    (source (graph core115) (root 8) 0 1) SmallGeFourSpectrum183.graph
      sourceMap115=true := by decide +kernel
theorem fusedMap115_checked : acceptsGraphIso
    (fused (graph core115) (root 8) 0 1) SmallGeFourSpectrum109.graph
      fusedMap115=true := by decide +kernel
theorem certified115 : Certified (graph core115) (root 8) 0 1 :=
  of_native_maps core115 SmallGeFourSpectrum183.graph SmallGeFourSpectrum109.graph
    sourceMap115 fusedMap115 sourceMap115_checked fusedMap115_checked
    SmallGeFourComparisons.comparison115
#print axioms sourceMap115_checked
#print axioms fusedMap115_checked
#print axioms certified115
def sourceMap115swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,2,3,7] (sourceLabel 8 1 0 v)
def fusedMap115swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,4,5,6,1,2,3] (fusedLabel 8 1 0 v)
theorem sourceMap115swap_checked : acceptsGraphIso
    (source (graph core115) (root 8) 1 0) SmallGeFourSpectrum183.graph
      sourceMap115swap=true := by decide +kernel
theorem fusedMap115swap_checked : acceptsGraphIso
    (fused (graph core115) (root 8) 1 0) SmallGeFourSpectrum109.graph
      fusedMap115swap=true := by decide +kernel
theorem certified115swap : Certified (graph core115) (root 8) 1 0 :=
  of_native_maps core115 SmallGeFourSpectrum183.graph SmallGeFourSpectrum109.graph
    sourceMap115swap fusedMap115swap sourceMap115swap_checked fusedMap115swap_checked
    SmallGeFourComparisons.comparison115
#print axioms sourceMap115swap_checked
#print axioms fusedMap115swap_checked
#print axioms certified115swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
