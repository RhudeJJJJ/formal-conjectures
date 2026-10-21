/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core141 : Family 8 := level8.get ⟨261,by decide⟩
def sourceMap141 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,7,8,5,6] (sourceLabel 8 0 1 v)
def fusedMap141 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,7,8,9,10,11,4,5,6] (fusedLabel 8 0 1 v)
theorem sourceMap141_checked : acceptsGraphIso
    (source (graph core141) (root 8) 0 1) SmallGeFourSpectrum164.graph
      sourceMap141=true := by decide +kernel
theorem fusedMap141_checked : acceptsGraphIso
    (fused (graph core141) (root 8) 0 1) SmallGeFourSpectrum194.graph
      fusedMap141=true := by decide +kernel
theorem certified141 : Certified (graph core141) (root 8) 0 1 :=
  of_native_maps core141 SmallGeFourSpectrum164.graph SmallGeFourSpectrum194.graph
    sourceMap141 fusedMap141 sourceMap141_checked fusedMap141_checked
    SmallGeFourComparisons.comparison141
#print axioms sourceMap141_checked
#print axioms fusedMap141_checked
#print axioms certified141
def sourceMap141swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,7,5,6,8] (sourceLabel 8 1 0 v)
def fusedMap141swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,7,8,9,10,11,4,5,6] (fusedLabel 8 1 0 v)
theorem sourceMap141swap_checked : acceptsGraphIso
    (source (graph core141) (root 8) 1 0) SmallGeFourSpectrum164.graph
      sourceMap141swap=true := by decide +kernel
theorem fusedMap141swap_checked : acceptsGraphIso
    (fused (graph core141) (root 8) 1 0) SmallGeFourSpectrum194.graph
      fusedMap141swap=true := by decide +kernel
theorem certified141swap : Certified (graph core141) (root 8) 1 0 :=
  of_native_maps core141 SmallGeFourSpectrum164.graph SmallGeFourSpectrum194.graph
    sourceMap141swap fusedMap141swap sourceMap141swap_checked fusedMap141swap_checked
    SmallGeFourComparisons.comparison141
#print axioms sourceMap141swap_checked
#print axioms fusedMap141swap_checked
#print axioms certified141swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
