/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core147 : Family 8 := level8.get ⟨270,by decide⟩
def sourceMap147 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,6,7] (sourceLabel 8 0 1 v)
def fusedMap147 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap147_checked : acceptsGraphIso
    (source (graph core147) (root 8) 0 1) SmallGeFourSpectrum216.graph
      sourceMap147=true := by decide +kernel
theorem fusedMap147_checked : acceptsGraphIso
    (fused (graph core147) (root 8) 0 1) SmallGeFourSpectrum129.graph
      fusedMap147=true := by decide +kernel
theorem certified147 : Certified (graph core147) (root 8) 0 1 :=
  of_native_maps core147 SmallGeFourSpectrum216.graph SmallGeFourSpectrum129.graph
    sourceMap147 fusedMap147 sourceMap147_checked fusedMap147_checked
    SmallGeFourComparisons.comparison147
#print axioms sourceMap147_checked
#print axioms fusedMap147_checked
#print axioms certified147
def sourceMap147swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,8,9,10,6,7,11] (sourceLabel 8 1 0 v)
def fusedMap147swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap147swap_checked : acceptsGraphIso
    (source (graph core147) (root 8) 1 0) SmallGeFourSpectrum216.graph
      sourceMap147swap=true := by decide +kernel
theorem fusedMap147swap_checked : acceptsGraphIso
    (fused (graph core147) (root 8) 1 0) SmallGeFourSpectrum129.graph
      fusedMap147swap=true := by decide +kernel
theorem certified147swap : Certified (graph core147) (root 8) 1 0 :=
  of_native_maps core147 SmallGeFourSpectrum216.graph SmallGeFourSpectrum129.graph
    sourceMap147swap fusedMap147swap sourceMap147swap_checked fusedMap147swap_checked
    SmallGeFourComparisons.comparison147
#print axioms sourceMap147swap_checked
#print axioms fusedMap147swap_checked
#print axioms certified147swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
