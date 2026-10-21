/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core143 : Family 8 := level8.get ⟨262,by decide⟩
def sourceMap143 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,5,6,7,8,3,4] (sourceLabel 8 0 1 v)
def fusedMap143 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,7,8,9,10,11,4,5,6] (fusedLabel 8 0 1 v)
theorem sourceMap143_checked : acceptsGraphIso
    (source (graph core143) (root 8) 0 1) SmallGeFourSpectrum167.graph
      sourceMap143=true := by decide +kernel
theorem fusedMap143_checked : acceptsGraphIso
    (fused (graph core143) (root 8) 0 1) SmallGeFourSpectrum195.graph
      fusedMap143=true := by decide +kernel
theorem certified143 : Certified (graph core143) (root 8) 0 1 :=
  of_native_maps core143 SmallGeFourSpectrum167.graph SmallGeFourSpectrum195.graph
    sourceMap143 fusedMap143 sourceMap143_checked fusedMap143_checked
    SmallGeFourComparisons.comparison143
#print axioms sourceMap143_checked
#print axioms fusedMap143_checked
#print axioms certified143
def sourceMap143swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,5,6,7,3,4,8] (sourceLabel 8 1 0 v)
def fusedMap143swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,7,8,9,10,11,4,5,6] (fusedLabel 8 1 0 v)
theorem sourceMap143swap_checked : acceptsGraphIso
    (source (graph core143) (root 8) 1 0) SmallGeFourSpectrum167.graph
      sourceMap143swap=true := by decide +kernel
theorem fusedMap143swap_checked : acceptsGraphIso
    (fused (graph core143) (root 8) 1 0) SmallGeFourSpectrum195.graph
      fusedMap143swap=true := by decide +kernel
theorem certified143swap : Certified (graph core143) (root 8) 1 0 :=
  of_native_maps core143 SmallGeFourSpectrum167.graph SmallGeFourSpectrum195.graph
    sourceMap143swap fusedMap143swap sourceMap143swap_checked fusedMap143swap_checked
    SmallGeFourComparisons.comparison143
#print axioms sourceMap143swap_checked
#print axioms fusedMap143swap_checked
#print axioms certified143swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
