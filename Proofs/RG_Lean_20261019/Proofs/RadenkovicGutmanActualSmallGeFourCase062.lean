/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core062 : Family 7 := level7.get ⟨61,by decide⟩
def sourceMap062 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,8,9,10,11,4,5,6,7,1,2,3] (sourceLabel 7 0 2 v)
def fusedMap062 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,9,10,11,5,6,7,8] (fusedLabel 7 0 2 v)
theorem sourceMap062_checked : acceptsGraphIso
    (source (graph core062) (root 7) 0 2) SmallGeFourSpectrum108.graph
      sourceMap062=true := by decide +kernel
theorem fusedMap062_checked : acceptsGraphIso
    (fused (graph core062) (root 7) 0 2) SmallGeFourSpectrum111.graph
      fusedMap062=true := by decide +kernel
theorem certified062 : Certified (graph core062) (root 7) 0 2 :=
  of_native_maps core062 SmallGeFourSpectrum108.graph SmallGeFourSpectrum111.graph
    sourceMap062 fusedMap062 sourceMap062_checked fusedMap062_checked
    SmallGeFourComparisons.comparison062
#print axioms sourceMap062_checked
#print axioms fusedMap062_checked
#print axioms certified062
def sourceMap062swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,4,5,6,1,2,3,7] (sourceLabel 7 2 0 v)
def fusedMap062swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,9,10,11,5,6,7,8] (fusedLabel 7 2 0 v)
theorem sourceMap062swap_checked : acceptsGraphIso
    (source (graph core062) (root 7) 2 0) SmallGeFourSpectrum108.graph
      sourceMap062swap=true := by decide +kernel
theorem fusedMap062swap_checked : acceptsGraphIso
    (fused (graph core062) (root 7) 2 0) SmallGeFourSpectrum111.graph
      fusedMap062swap=true := by decide +kernel
theorem certified062swap : Certified (graph core062) (root 7) 2 0 :=
  of_native_maps core062 SmallGeFourSpectrum108.graph SmallGeFourSpectrum111.graph
    sourceMap062swap fusedMap062swap sourceMap062swap_checked fusedMap062swap_checked
    SmallGeFourComparisons.comparison062
#print axioms sourceMap062swap_checked
#print axioms fusedMap062swap_checked
#print axioms certified062swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
