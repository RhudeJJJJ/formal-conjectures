/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core121 : Family 8 := level8.get ⟨206,by decide⟩
def sourceMap121 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (sourceLabel 8 0 1 v)
def fusedMap121 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8] (fusedLabel 8 0 1 v)
theorem sourceMap121_checked : acceptsGraphIso
    (source (graph core121) (root 8) 0 1) SmallGeFourSpectrum136.graph
      sourceMap121=true := by decide +kernel
theorem fusedMap121_checked : acceptsGraphIso
    (fused (graph core121) (root 8) 0 1) SmallGeFourSpectrum138.graph
      fusedMap121=true := by decide +kernel
theorem certified121 : Certified (graph core121) (root 8) 0 1 :=
  of_native_maps core121 SmallGeFourSpectrum136.graph SmallGeFourSpectrum138.graph
    sourceMap121 fusedMap121 sourceMap121_checked fusedMap121_checked
    SmallGeFourComparisons.comparison121
#print axioms sourceMap121_checked
#print axioms fusedMap121_checked
#print axioms certified121
def sourceMap121swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7,11] (sourceLabel 8 1 0 v)
def fusedMap121swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8] (fusedLabel 8 1 0 v)
theorem sourceMap121swap_checked : acceptsGraphIso
    (source (graph core121) (root 8) 1 0) SmallGeFourSpectrum136.graph
      sourceMap121swap=true := by decide +kernel
theorem fusedMap121swap_checked : acceptsGraphIso
    (fused (graph core121) (root 8) 1 0) SmallGeFourSpectrum138.graph
      fusedMap121swap=true := by decide +kernel
theorem certified121swap : Certified (graph core121) (root 8) 1 0 :=
  of_native_maps core121 SmallGeFourSpectrum136.graph SmallGeFourSpectrum138.graph
    sourceMap121swap fusedMap121swap sourceMap121swap_checked fusedMap121swap_checked
    SmallGeFourComparisons.comparison121
#print axioms sourceMap121swap_checked
#print axioms fusedMap121swap_checked
#print axioms certified121swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
