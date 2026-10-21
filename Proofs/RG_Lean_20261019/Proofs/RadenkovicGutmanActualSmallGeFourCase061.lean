/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core061 : Family 7 := level7.get ⟨61,by decide⟩
def sourceMap061 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,8,9,10,4,5,6,7,2,3] (sourceLabel 7 0 1 v)
def fusedMap061 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,7,8,9,10,4,5,6,1,2,3] (fusedLabel 7 0 1 v)
theorem sourceMap061_checked : acceptsGraphIso
    (source (graph core061) (root 7) 0 1) SmallGeFourSpectrum062.graph
      sourceMap061=true := by decide +kernel
theorem fusedMap061_checked : acceptsGraphIso
    (fused (graph core061) (root 7) 0 1) SmallGeFourSpectrum039.graph
      fusedMap061=true := by decide +kernel
theorem certified061 : Certified (graph core061) (root 7) 0 1 :=
  of_native_maps core061 SmallGeFourSpectrum062.graph SmallGeFourSpectrum039.graph
    sourceMap061 fusedMap061 sourceMap061_checked fusedMap061_checked
    SmallGeFourComparisons.comparison061
#print axioms sourceMap061_checked
#print axioms fusedMap061_checked
#print axioms certified061
def sourceMap061swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,8,9,10,4,5,6,2,3,7] (sourceLabel 7 1 0 v)
def fusedMap061swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,7,8,9,10,4,5,6,1,2,3] (fusedLabel 7 1 0 v)
theorem sourceMap061swap_checked : acceptsGraphIso
    (source (graph core061) (root 7) 1 0) SmallGeFourSpectrum062.graph
      sourceMap061swap=true := by decide +kernel
theorem fusedMap061swap_checked : acceptsGraphIso
    (fused (graph core061) (root 7) 1 0) SmallGeFourSpectrum039.graph
      fusedMap061swap=true := by decide +kernel
theorem certified061swap : Certified (graph core061) (root 7) 1 0 :=
  of_native_maps core061 SmallGeFourSpectrum062.graph SmallGeFourSpectrum039.graph
    sourceMap061swap fusedMap061swap sourceMap061swap_checked fusedMap061swap_checked
    SmallGeFourComparisons.comparison061
#print axioms sourceMap061swap_checked
#print axioms fusedMap061swap_checked
#print axioms certified061swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
