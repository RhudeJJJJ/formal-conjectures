/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core137 : Family 8 := level8.get ⟨256,by decide⟩
def sourceMap137 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,7,8] (sourceLabel 8 0 1 v)
def fusedMap137 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9] (fusedLabel 8 0 1 v)
theorem sourceMap137_checked : acceptsGraphIso
    (source (graph core137) (root 8) 0 1) SmallGeFourSpectrum195.graph
      sourceMap137=true := by decide +kernel
theorem fusedMap137_checked : acceptsGraphIso
    (fused (graph core137) (root 8) 0 1) SmallGeFourSpectrum192.graph
      fusedMap137=true := by decide +kernel
theorem certified137 : Certified (graph core137) (root 8) 0 1 :=
  of_native_maps core137 SmallGeFourSpectrum195.graph SmallGeFourSpectrum192.graph
    sourceMap137 fusedMap137 sourceMap137_checked fusedMap137_checked
    SmallGeFourComparisons.comparison137
#print axioms sourceMap137_checked
#print axioms fusedMap137_checked
#print axioms certified137
def sourceMap137swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,9,10,7,8,11] (sourceLabel 8 1 0 v)
def fusedMap137swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9] (fusedLabel 8 1 0 v)
theorem sourceMap137swap_checked : acceptsGraphIso
    (source (graph core137) (root 8) 1 0) SmallGeFourSpectrum195.graph
      sourceMap137swap=true := by decide +kernel
theorem fusedMap137swap_checked : acceptsGraphIso
    (fused (graph core137) (root 8) 1 0) SmallGeFourSpectrum192.graph
      fusedMap137swap=true := by decide +kernel
theorem certified137swap : Certified (graph core137) (root 8) 1 0 :=
  of_native_maps core137 SmallGeFourSpectrum195.graph SmallGeFourSpectrum192.graph
    sourceMap137swap fusedMap137swap sourceMap137swap_checked fusedMap137swap_checked
    SmallGeFourComparisons.comparison137
#print axioms sourceMap137swap_checked
#print axioms fusedMap137swap_checked
#print axioms certified137swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
