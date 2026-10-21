/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core053 : Family 6 := level6.get ⟨46,by decide⟩
def sourceMap053 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,5,6,7,8,3,4,9,10,11] (sourceLabel 6 1 2 v)
def fusedMap053 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap053_checked : acceptsGraphIso
    (source (graph core053) (root 6) 1 2) SmallGeFourSpectrum167.graph
      sourceMap053=true := by decide +kernel
theorem fusedMap053_checked : acceptsGraphIso
    (fused (graph core053) (root 6) 1 2) SmallGeFourSpectrum100.graph
      fusedMap053=true := by decide +kernel
theorem certified053 : Certified (graph core053) (root 6) 1 2 :=
  of_native_maps core053 SmallGeFourSpectrum167.graph SmallGeFourSpectrum100.graph
    sourceMap053 fusedMap053 sourceMap053_checked fusedMap053_checked
    SmallGeFourComparisons.comparison053
#print axioms sourceMap053_checked
#print axioms fusedMap053_checked
#print axioms certified053
def sourceMap053swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,5,6,7,8,9,10,11,3,4] (sourceLabel 6 2 1 v)
def fusedMap053swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap053swap_checked : acceptsGraphIso
    (source (graph core053) (root 6) 2 1) SmallGeFourSpectrum167.graph
      sourceMap053swap=true := by decide +kernel
theorem fusedMap053swap_checked : acceptsGraphIso
    (fused (graph core053) (root 6) 2 1) SmallGeFourSpectrum100.graph
      fusedMap053swap=true := by decide +kernel
theorem certified053swap : Certified (graph core053) (root 6) 2 1 :=
  of_native_maps core053 SmallGeFourSpectrum167.graph SmallGeFourSpectrum100.graph
    sourceMap053swap fusedMap053swap sourceMap053swap_checked fusedMap053swap_checked
    SmallGeFourComparisons.comparison053
#print axioms sourceMap053swap_checked
#print axioms fusedMap053swap_checked
#print axioms certified053swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
