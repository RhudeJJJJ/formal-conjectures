/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core094 : Family 7 := level7.get ⟨111,by decide⟩
def sourceMap094 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 0 2 v)
def fusedMap094 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap094_checked : acceptsGraphIso
    (source (graph core094) (root 7) 0 2) SmallGeFourSpectrum164.graph
      sourceMap094=true := by decide +kernel
theorem fusedMap094_checked : acceptsGraphIso
    (fused (graph core094) (root 7) 0 2) SmallGeFourSpectrum166.graph
      fusedMap094=true := by decide +kernel
theorem certified094 : Certified (graph core094) (root 7) 0 2 :=
  of_native_maps core094 SmallGeFourSpectrum164.graph SmallGeFourSpectrum166.graph
    sourceMap094 fusedMap094 sourceMap094_checked fusedMap094_checked
    SmallGeFourComparisons.comparison094
#print axioms sourceMap094_checked
#print axioms fusedMap094_checked
#print axioms certified094
def sourceMap094swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,8] (sourceLabel 7 2 0 v)
def fusedMap094swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap094swap_checked : acceptsGraphIso
    (source (graph core094) (root 7) 2 0) SmallGeFourSpectrum164.graph
      sourceMap094swap=true := by decide +kernel
theorem fusedMap094swap_checked : acceptsGraphIso
    (fused (graph core094) (root 7) 2 0) SmallGeFourSpectrum166.graph
      fusedMap094swap=true := by decide +kernel
theorem certified094swap : Certified (graph core094) (root 7) 2 0 :=
  of_native_maps core094 SmallGeFourSpectrum164.graph SmallGeFourSpectrum166.graph
    sourceMap094swap fusedMap094swap sourceMap094swap_checked fusedMap094swap_checked
    SmallGeFourComparisons.comparison094
#print axioms sourceMap094swap_checked
#print axioms fusedMap094swap_checked
#print axioms certified094swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
