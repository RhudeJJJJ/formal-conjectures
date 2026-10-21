/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core157 : Family 8 := level8.get ⟨279,by decide⟩
def sourceMap157 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,6,7] (sourceLabel 8 0 1 v)
def fusedMap157 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap157_checked : acceptsGraphIso
    (source (graph core157) (root 8) 0 1) SmallGeFourSpectrum227.graph
      sourceMap157=true := by decide +kernel
theorem fusedMap157_checked : acceptsGraphIso
    (fused (graph core157) (root 8) 0 1) SmallGeFourSpectrum141.graph
      fusedMap157=true := by decide +kernel
theorem certified157 : Certified (graph core157) (root 8) 0 1 :=
  of_native_maps core157 SmallGeFourSpectrum227.graph SmallGeFourSpectrum141.graph
    sourceMap157 fusedMap157 sourceMap157_checked fusedMap157_checked
    SmallGeFourComparisons.comparison157
#print axioms sourceMap157_checked
#print axioms fusedMap157_checked
#print axioms certified157
def sourceMap157swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,8,9,10,6,7,11] (sourceLabel 8 1 0 v)
def fusedMap157swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap157swap_checked : acceptsGraphIso
    (source (graph core157) (root 8) 1 0) SmallGeFourSpectrum227.graph
      sourceMap157swap=true := by decide +kernel
theorem fusedMap157swap_checked : acceptsGraphIso
    (fused (graph core157) (root 8) 1 0) SmallGeFourSpectrum141.graph
      fusedMap157swap=true := by decide +kernel
theorem certified157swap : Certified (graph core157) (root 8) 1 0 :=
  of_native_maps core157 SmallGeFourSpectrum227.graph SmallGeFourSpectrum141.graph
    sourceMap157swap fusedMap157swap sourceMap157swap_checked fusedMap157swap_checked
    SmallGeFourComparisons.comparison157
#print axioms sourceMap157swap_checked
#print axioms fusedMap157swap_checked
#print axioms certified157swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
