/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core167 : Family 8 := level8.get ⟨284,by decide⟩
def sourceMap167 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,5,6,7,8,9,10,11,3,4] (sourceLabel 8 0 1 v)
def fusedMap167 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap167_checked : acceptsGraphIso
    (source (graph core167) (root 8) 0 1) SmallGeFourSpectrum232.graph
      sourceMap167=true := by decide +kernel
theorem fusedMap167_checked : acceptsGraphIso
    (fused (graph core167) (root 8) 0 1) SmallGeFourSpectrum178.graph
      fusedMap167=true := by decide +kernel
theorem certified167 : Certified (graph core167) (root 8) 0 1 :=
  of_native_maps core167 SmallGeFourSpectrum232.graph SmallGeFourSpectrum178.graph
    sourceMap167 fusedMap167 sourceMap167_checked fusedMap167_checked
    SmallGeFourComparisons.comparison167
#print axioms sourceMap167_checked
#print axioms fusedMap167_checked
#print axioms certified167
def sourceMap167swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,5,6,7,8,9,10,3,4,11] (sourceLabel 8 1 0 v)
def fusedMap167swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap167swap_checked : acceptsGraphIso
    (source (graph core167) (root 8) 1 0) SmallGeFourSpectrum232.graph
      sourceMap167swap=true := by decide +kernel
theorem fusedMap167swap_checked : acceptsGraphIso
    (fused (graph core167) (root 8) 1 0) SmallGeFourSpectrum178.graph
      fusedMap167swap=true := by decide +kernel
theorem certified167swap : Certified (graph core167) (root 8) 1 0 :=
  of_native_maps core167 SmallGeFourSpectrum232.graph SmallGeFourSpectrum178.graph
    sourceMap167swap fusedMap167swap sourceMap167swap_checked fusedMap167swap_checked
    SmallGeFourComparisons.comparison167
#print axioms sourceMap167swap_checked
#print axioms fusedMap167swap_checked
#print axioms certified167swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
