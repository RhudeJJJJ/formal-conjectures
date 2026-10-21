/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core153 : Family 8 := level8.get ⟨277,by decide⟩
def sourceMap153 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,7,8] (sourceLabel 8 0 1 v)
def fusedMap153 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap153_checked : acceptsGraphIso
    (source (graph core153) (root 8) 0 1) SmallGeFourSpectrum223.graph
      sourceMap153=true := by decide +kernel
theorem fusedMap153_checked : acceptsGraphIso
    (fused (graph core153) (root 8) 0 1) SmallGeFourSpectrum139.graph
      fusedMap153=true := by decide +kernel
theorem certified153 : Certified (graph core153) (root 8) 0 1 :=
  of_native_maps core153 SmallGeFourSpectrum223.graph SmallGeFourSpectrum139.graph
    sourceMap153 fusedMap153 sourceMap153_checked fusedMap153_checked
    SmallGeFourComparisons.comparison153
#print axioms sourceMap153_checked
#print axioms fusedMap153_checked
#print axioms certified153
def sourceMap153swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,9,10,7,8,11] (sourceLabel 8 1 0 v)
def fusedMap153swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap153swap_checked : acceptsGraphIso
    (source (graph core153) (root 8) 1 0) SmallGeFourSpectrum223.graph
      sourceMap153swap=true := by decide +kernel
theorem fusedMap153swap_checked : acceptsGraphIso
    (fused (graph core153) (root 8) 1 0) SmallGeFourSpectrum139.graph
      fusedMap153swap=true := by decide +kernel
theorem certified153swap : Certified (graph core153) (root 8) 1 0 :=
  of_native_maps core153 SmallGeFourSpectrum223.graph SmallGeFourSpectrum139.graph
    sourceMap153swap fusedMap153swap sourceMap153swap_checked fusedMap153swap_checked
    SmallGeFourComparisons.comparison153
#print axioms sourceMap153swap_checked
#print axioms fusedMap153swap_checked
#print axioms certified153swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
