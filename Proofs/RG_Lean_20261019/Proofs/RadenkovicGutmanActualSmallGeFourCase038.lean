/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core038 : Family 6 := level6.get ⟨43,by decide⟩
def sourceMap038 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 0 2 v)
def fusedMap038 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap038_checked : acceptsGraphIso
    (source (graph core038) (root 6) 0 2) SmallGeFourSpectrum048.graph
      sourceMap038=true := by decide +kernel
theorem fusedMap038_checked : acceptsGraphIso
    (fused (graph core038) (root 6) 0 2) SmallGeFourSpectrum049.graph
      fusedMap038=true := by decide +kernel
theorem certified038 : Certified (graph core038) (root 6) 0 2 :=
  of_native_maps core038 SmallGeFourSpectrum048.graph SmallGeFourSpectrum049.graph
    sourceMap038 fusedMap038 sourceMap038_checked fusedMap038_checked
    SmallGeFourComparisons.comparison038
#print axioms sourceMap038_checked
#print axioms fusedMap038_checked
#print axioms certified038
def sourceMap038swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,7] (sourceLabel 6 2 0 v)
def fusedMap038swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap038swap_checked : acceptsGraphIso
    (source (graph core038) (root 6) 2 0) SmallGeFourSpectrum048.graph
      sourceMap038swap=true := by decide +kernel
theorem fusedMap038swap_checked : acceptsGraphIso
    (fused (graph core038) (root 6) 2 0) SmallGeFourSpectrum049.graph
      fusedMap038swap=true := by decide +kernel
theorem certified038swap : Certified (graph core038) (root 6) 2 0 :=
  of_native_maps core038 SmallGeFourSpectrum048.graph SmallGeFourSpectrum049.graph
    sourceMap038swap fusedMap038swap sourceMap038swap_checked fusedMap038swap_checked
    SmallGeFourComparisons.comparison038
#print axioms sourceMap038swap_checked
#print axioms fusedMap038swap_checked
#print axioms certified038swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
