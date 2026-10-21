/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core155 : Family 8 := level8.get ⟨278,by decide⟩
def sourceMap155 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,8,9] (sourceLabel 8 0 1 v)
def fusedMap155 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap155_checked : acceptsGraphIso
    (source (graph core155) (root 8) 0 1) SmallGeFourSpectrum226.graph
      sourceMap155=true := by decide +kernel
theorem fusedMap155_checked : acceptsGraphIso
    (fused (graph core155) (root 8) 0 1) SmallGeFourSpectrum140.graph
      fusedMap155=true := by decide +kernel
theorem certified155 : Certified (graph core155) (root 8) 0 1 :=
  of_native_maps core155 SmallGeFourSpectrum226.graph SmallGeFourSpectrum140.graph
    sourceMap155 fusedMap155 sourceMap155_checked fusedMap155_checked
    SmallGeFourComparisons.comparison155
#print axioms sourceMap155_checked
#print axioms fusedMap155_checked
#print axioms certified155
def sourceMap155swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11] (sourceLabel 8 1 0 v)
def fusedMap155swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap155swap_checked : acceptsGraphIso
    (source (graph core155) (root 8) 1 0) SmallGeFourSpectrum226.graph
      sourceMap155swap=true := by decide +kernel
theorem fusedMap155swap_checked : acceptsGraphIso
    (fused (graph core155) (root 8) 1 0) SmallGeFourSpectrum140.graph
      fusedMap155swap=true := by decide +kernel
theorem certified155swap : Certified (graph core155) (root 8) 1 0 :=
  of_native_maps core155 SmallGeFourSpectrum226.graph SmallGeFourSpectrum140.graph
    sourceMap155swap fusedMap155swap sourceMap155swap_checked fusedMap155swap_checked
    SmallGeFourComparisons.comparison155
#print axioms sourceMap155swap_checked
#print axioms fusedMap155swap_checked
#print axioms certified155swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
