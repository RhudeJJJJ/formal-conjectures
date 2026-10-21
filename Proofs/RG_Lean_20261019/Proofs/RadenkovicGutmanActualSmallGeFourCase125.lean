/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core125 : Family 8 := level8.get ⟨228,by decide⟩
def sourceMap125 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![4,0,1,2,3,5,6,9,10,11,7,8] (sourceLabel 8 0 1 v)
def fusedMap125 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7] (fusedLabel 8 0 1 v)
theorem sourceMap125_checked : acceptsGraphIso
    (source (graph core125) (root 8) 0 1) SmallGeFourSpectrum156.graph
      sourceMap125=true := by decide +kernel
theorem fusedMap125_checked : acceptsGraphIso
    (fused (graph core125) (root 8) 0 1) SmallGeFourSpectrum161.graph
      fusedMap125=true := by decide +kernel
theorem certified125 : Certified (graph core125) (root 8) 0 1 :=
  of_native_maps core125 SmallGeFourSpectrum156.graph SmallGeFourSpectrum161.graph
    sourceMap125 fusedMap125 sourceMap125_checked fusedMap125_checked
    SmallGeFourComparisons.comparison125
#print axioms sourceMap125_checked
#print axioms fusedMap125_checked
#print axioms certified125
def sourceMap125swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![4,0,1,2,3,5,6,9,10,7,8,11] (sourceLabel 8 1 0 v)
def fusedMap125swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7] (fusedLabel 8 1 0 v)
theorem sourceMap125swap_checked : acceptsGraphIso
    (source (graph core125) (root 8) 1 0) SmallGeFourSpectrum156.graph
      sourceMap125swap=true := by decide +kernel
theorem fusedMap125swap_checked : acceptsGraphIso
    (fused (graph core125) (root 8) 1 0) SmallGeFourSpectrum161.graph
      fusedMap125swap=true := by decide +kernel
theorem certified125swap : Certified (graph core125) (root 8) 1 0 :=
  of_native_maps core125 SmallGeFourSpectrum156.graph SmallGeFourSpectrum161.graph
    sourceMap125swap fusedMap125swap sourceMap125swap_checked fusedMap125swap_checked
    SmallGeFourComparisons.comparison125
#print axioms sourceMap125swap_checked
#print axioms fusedMap125swap_checked
#print axioms certified125swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
