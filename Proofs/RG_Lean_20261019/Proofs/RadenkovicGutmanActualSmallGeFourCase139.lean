/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core139 : Family 8 := level8.get ⟨260,by decide⟩
def sourceMap139 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,6,7,8,4,5] (sourceLabel 8 0 1 v)
def fusedMap139 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,7,8,9,10,11,4,5,6] (fusedLabel 8 0 1 v)
theorem sourceMap139_checked : acceptsGraphIso
    (source (graph core139) (root 8) 0 1) SmallGeFourSpectrum141.graph
      sourceMap139=true := by decide +kernel
theorem fusedMap139_checked : acceptsGraphIso
    (fused (graph core139) (root 8) 0 1) SmallGeFourSpectrum193.graph
      fusedMap139=true := by decide +kernel
theorem certified139 : Certified (graph core139) (root 8) 0 1 :=
  of_native_maps core139 SmallGeFourSpectrum141.graph SmallGeFourSpectrum193.graph
    sourceMap139 fusedMap139 sourceMap139_checked fusedMap139_checked
    SmallGeFourComparisons.comparison139
#print axioms sourceMap139_checked
#print axioms fusedMap139_checked
#print axioms certified139
def sourceMap139swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,6,7,4,5,8] (sourceLabel 8 1 0 v)
def fusedMap139swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,7,8,9,10,11,4,5,6] (fusedLabel 8 1 0 v)
theorem sourceMap139swap_checked : acceptsGraphIso
    (source (graph core139) (root 8) 1 0) SmallGeFourSpectrum141.graph
      sourceMap139swap=true := by decide +kernel
theorem fusedMap139swap_checked : acceptsGraphIso
    (fused (graph core139) (root 8) 1 0) SmallGeFourSpectrum193.graph
      fusedMap139swap=true := by decide +kernel
theorem certified139swap : Certified (graph core139) (root 8) 1 0 :=
  of_native_maps core139 SmallGeFourSpectrum141.graph SmallGeFourSpectrum193.graph
    sourceMap139swap fusedMap139swap sourceMap139swap_checked fusedMap139swap_checked
    SmallGeFourComparisons.comparison139
#print axioms sourceMap139swap_checked
#print axioms fusedMap139swap_checked
#print axioms certified139swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
