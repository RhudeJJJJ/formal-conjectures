/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core109 : Family 8 := level8.get ⟨94,by decide⟩
def sourceMap109 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (sourceLabel 8 0 1 v)
def fusedMap109 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,2,3,4] (fusedLabel 8 0 1 v)
theorem sourceMap109_checked : acceptsGraphIso
    (source (graph core109) (root 8) 0 1) SmallGeFourSpectrum100.graph
      sourceMap109=true := by decide +kernel
theorem fusedMap109_checked : acceptsGraphIso
    (fused (graph core109) (root 8) 0 1) SmallGeFourSpectrum110.graph
      fusedMap109=true := by decide +kernel
theorem certified109 : Certified (graph core109) (root 8) 0 1 :=
  of_native_maps core109 SmallGeFourSpectrum100.graph SmallGeFourSpectrum110.graph
    sourceMap109 fusedMap109 sourceMap109_checked fusedMap109_checked
    SmallGeFourComparisons.comparison109
#print axioms sourceMap109_checked
#print axioms fusedMap109_checked
#print axioms certified109
def sourceMap109swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,2,3,7] (sourceLabel 8 1 0 v)
def fusedMap109swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,2,3,4] (fusedLabel 8 1 0 v)
theorem sourceMap109swap_checked : acceptsGraphIso
    (source (graph core109) (root 8) 1 0) SmallGeFourSpectrum100.graph
      sourceMap109swap=true := by decide +kernel
theorem fusedMap109swap_checked : acceptsGraphIso
    (fused (graph core109) (root 8) 1 0) SmallGeFourSpectrum110.graph
      fusedMap109swap=true := by decide +kernel
theorem certified109swap : Certified (graph core109) (root 8) 1 0 :=
  of_native_maps core109 SmallGeFourSpectrum100.graph SmallGeFourSpectrum110.graph
    sourceMap109swap fusedMap109swap sourceMap109swap_checked fusedMap109swap_checked
    SmallGeFourComparisons.comparison109
#print axioms sourceMap109swap_checked
#print axioms fusedMap109swap_checked
#print axioms certified109swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
