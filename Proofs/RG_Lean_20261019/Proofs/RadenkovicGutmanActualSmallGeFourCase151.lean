/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core151 : Family 8 := level8.get ⟨275,by decide⟩
def sourceMap151 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,7,8,9,10,11,5,6] (sourceLabel 8 0 1 v)
def fusedMap151 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap151_checked : acceptsGraphIso
    (source (graph core151) (root 8) 0 1) SmallGeFourSpectrum221.graph
      sourceMap151=true := by decide +kernel
theorem fusedMap151_checked : acceptsGraphIso
    (fused (graph core151) (root 8) 0 1) SmallGeFourSpectrum132.graph
      fusedMap151=true := by decide +kernel
theorem certified151 : Certified (graph core151) (root 8) 0 1 :=
  of_native_maps core151 SmallGeFourSpectrum221.graph SmallGeFourSpectrum132.graph
    sourceMap151 fusedMap151 sourceMap151_checked fusedMap151_checked
    SmallGeFourComparisons.comparison151
#print axioms sourceMap151_checked
#print axioms fusedMap151_checked
#print axioms certified151
def sourceMap151swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,7,8,9,10,5,6,11] (sourceLabel 8 1 0 v)
def fusedMap151swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap151swap_checked : acceptsGraphIso
    (source (graph core151) (root 8) 1 0) SmallGeFourSpectrum221.graph
      sourceMap151swap=true := by decide +kernel
theorem fusedMap151swap_checked : acceptsGraphIso
    (fused (graph core151) (root 8) 1 0) SmallGeFourSpectrum132.graph
      fusedMap151swap=true := by decide +kernel
theorem certified151swap : Certified (graph core151) (root 8) 1 0 :=
  of_native_maps core151 SmallGeFourSpectrum221.graph SmallGeFourSpectrum132.graph
    sourceMap151swap fusedMap151swap sourceMap151swap_checked fusedMap151swap_checked
    SmallGeFourComparisons.comparison151
#print axioms sourceMap151swap_checked
#print axioms fusedMap151swap_checked
#print axioms certified151swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
