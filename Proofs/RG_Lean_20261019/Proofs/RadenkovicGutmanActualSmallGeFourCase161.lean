/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core161 : Family 8 := level8.get ⟨281,by decide⟩
def sourceMap161 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap161 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap161_checked : acceptsGraphIso
    (source (graph core161) (root 8) 0 1) SmallGeFourSpectrum229.graph
      sourceMap161=true := by decide +kernel
theorem fusedMap161_checked : acceptsGraphIso
    (fused (graph core161) (root 8) 0 1) SmallGeFourSpectrum163.graph
      fusedMap161=true := by decide +kernel
theorem certified161 : Certified (graph core161) (root 8) 0 1 :=
  of_native_maps core161 SmallGeFourSpectrum229.graph SmallGeFourSpectrum163.graph
    sourceMap161 fusedMap161 sourceMap161_checked fusedMap161_checked
    SmallGeFourComparisons.comparison161
#print axioms sourceMap161_checked
#print axioms fusedMap161_checked
#print axioms certified161
def sourceMap161swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap161swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap161swap_checked : acceptsGraphIso
    (source (graph core161) (root 8) 1 0) SmallGeFourSpectrum229.graph
      sourceMap161swap=true := by decide +kernel
theorem fusedMap161swap_checked : acceptsGraphIso
    (fused (graph core161) (root 8) 1 0) SmallGeFourSpectrum163.graph
      fusedMap161swap=true := by decide +kernel
theorem certified161swap : Certified (graph core161) (root 8) 1 0 :=
  of_native_maps core161 SmallGeFourSpectrum229.graph SmallGeFourSpectrum163.graph
    sourceMap161swap fusedMap161swap sourceMap161swap_checked fusedMap161swap_checked
    SmallGeFourComparisons.comparison161
#print axioms sourceMap161swap_checked
#print axioms fusedMap161swap_checked
#print axioms certified161swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
