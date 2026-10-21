/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core219 : Family 9 := level9.get ⟨673,by decide⟩
def sourceMap219 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap219 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,8,9,10,11,3,4,5,6,7,1,2] (fusedLabel 9 0 0 v)
theorem sourceMap219_checked : acceptsGraphIso
    (source (graph core219) (root 9) 0 0) SmallGeFourSpectrum202.graph
      sourceMap219=true := by decide +kernel
theorem fusedMap219_checked : acceptsGraphIso
    (fused (graph core219) (root 9) 0 0) SmallGeFourSpectrum179.graph
      fusedMap219=true := by decide +kernel
theorem certified219 : Certified (graph core219) (root 9) 0 0 :=
  of_native_maps core219 SmallGeFourSpectrum202.graph SmallGeFourSpectrum179.graph
    sourceMap219 fusedMap219 sourceMap219_checked fusedMap219_checked
    SmallGeFourComparisons.comparison219
#print axioms sourceMap219_checked
#print axioms fusedMap219_checked
#print axioms certified219
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
