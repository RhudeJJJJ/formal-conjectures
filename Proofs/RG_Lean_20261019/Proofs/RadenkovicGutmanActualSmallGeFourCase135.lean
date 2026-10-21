/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core135 : Family 8 := level8.get ⟨254,by decide⟩
def sourceMap135 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,8,9,10,11,3,4,5,6,7,1,2] (sourceLabel 8 0 1 v)
def fusedMap135 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7] (fusedLabel 8 0 1 v)
theorem sourceMap135_checked : acceptsGraphIso
    (source (graph core135) (root 8) 0 1) SmallGeFourSpectrum179.graph
      sourceMap135=true := by decide +kernel
theorem fusedMap135_checked : acceptsGraphIso
    (fused (graph core135) (root 8) 0 1) SmallGeFourSpectrum191.graph
      fusedMap135=true := by decide +kernel
theorem certified135 : Certified (graph core135) (root 8) 0 1 :=
  of_native_maps core135 SmallGeFourSpectrum179.graph SmallGeFourSpectrum191.graph
    sourceMap135 fusedMap135 sourceMap135_checked fusedMap135_checked
    SmallGeFourComparisons.comparison135
#print axioms sourceMap135_checked
#print axioms fusedMap135_checked
#print axioms certified135
def sourceMap135swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,3,4,5,6,1,2,7] (sourceLabel 8 1 0 v)
def fusedMap135swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7] (fusedLabel 8 1 0 v)
theorem sourceMap135swap_checked : acceptsGraphIso
    (source (graph core135) (root 8) 1 0) SmallGeFourSpectrum179.graph
      sourceMap135swap=true := by decide +kernel
theorem fusedMap135swap_checked : acceptsGraphIso
    (fused (graph core135) (root 8) 1 0) SmallGeFourSpectrum191.graph
      fusedMap135swap=true := by decide +kernel
theorem certified135swap : Certified (graph core135) (root 8) 1 0 :=
  of_native_maps core135 SmallGeFourSpectrum179.graph SmallGeFourSpectrum191.graph
    sourceMap135swap fusedMap135swap sourceMap135swap_checked fusedMap135swap_checked
    SmallGeFourComparisons.comparison135
#print axioms sourceMap135swap_checked
#print axioms fusedMap135swap_checked
#print axioms certified135swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
