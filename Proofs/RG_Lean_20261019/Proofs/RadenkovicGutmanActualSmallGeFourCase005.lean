/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core005 : Family 4 := level4.get ⟨8,by decide⟩
def sourceMap005 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (sourceLabel 4 0 5 v)
def fusedMap005 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11] (fusedLabel 4 0 5 v)
theorem sourceMap005_checked : acceptsGraphIso
    (source (graph core005) (root 4) 0 5) SmallGeFourSpectrum093.graph
      sourceMap005=true := by decide +kernel
theorem fusedMap005_checked : acceptsGraphIso
    (fused (graph core005) (root 4) 0 5) SmallGeFourSpectrum094.graph
      fusedMap005=true := by decide +kernel
theorem certified005 : Certified (graph core005) (root 4) 0 5 :=
  of_native_maps core005 SmallGeFourSpectrum093.graph SmallGeFourSpectrum094.graph
    sourceMap005 fusedMap005 sourceMap005_checked fusedMap005_checked
    SmallGeFourComparisons.comparison005
#print axioms sourceMap005_checked
#print axioms fusedMap005_checked
#print axioms certified005
def sourceMap005swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,8,9,10,11,7] (sourceLabel 4 5 0 v)
def fusedMap005swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11] (fusedLabel 4 5 0 v)
theorem sourceMap005swap_checked : acceptsGraphIso
    (source (graph core005) (root 4) 5 0) SmallGeFourSpectrum093.graph
      sourceMap005swap=true := by decide +kernel
theorem fusedMap005swap_checked : acceptsGraphIso
    (fused (graph core005) (root 4) 5 0) SmallGeFourSpectrum094.graph
      fusedMap005swap=true := by decide +kernel
theorem certified005swap : Certified (graph core005) (root 4) 5 0 :=
  of_native_maps core005 SmallGeFourSpectrum093.graph SmallGeFourSpectrum094.graph
    sourceMap005swap fusedMap005swap sourceMap005swap_checked fusedMap005swap_checked
    SmallGeFourComparisons.comparison005
#print axioms sourceMap005swap_checked
#print axioms fusedMap005swap_checked
#print axioms certified005swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
