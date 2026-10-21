/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core051 : Family 6 := level6.get ⟨46,by decide⟩
def sourceMap051 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (sourceLabel 6 0 3 v)
def fusedMap051 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap051_checked : acceptsGraphIso
    (source (graph core051) (root 6) 0 3) SmallGeFourSpectrum180.graph
      sourceMap051=true := by decide +kernel
theorem fusedMap051_checked : acceptsGraphIso
    (fused (graph core051) (root 6) 0 3) SmallGeFourSpectrum100.graph
      fusedMap051=true := by decide +kernel
theorem certified051 : Certified (graph core051) (root 6) 0 3 :=
  of_native_maps core051 SmallGeFourSpectrum180.graph SmallGeFourSpectrum100.graph
    sourceMap051 fusedMap051 sourceMap051_checked fusedMap051_checked
    SmallGeFourComparisons.comparison051
#print axioms sourceMap051_checked
#print axioms fusedMap051_checked
#print axioms certified051
def sourceMap051swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,8] (sourceLabel 6 3 0 v)
def fusedMap051swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap051swap_checked : acceptsGraphIso
    (source (graph core051) (root 6) 3 0) SmallGeFourSpectrum180.graph
      sourceMap051swap=true := by decide +kernel
theorem fusedMap051swap_checked : acceptsGraphIso
    (fused (graph core051) (root 6) 3 0) SmallGeFourSpectrum100.graph
      fusedMap051swap=true := by decide +kernel
theorem certified051swap : Certified (graph core051) (root 6) 3 0 :=
  of_native_maps core051 SmallGeFourSpectrum180.graph SmallGeFourSpectrum100.graph
    sourceMap051swap fusedMap051swap sourceMap051swap_checked fusedMap051swap_checked
    SmallGeFourComparisons.comparison051
#print axioms sourceMap051swap_checked
#print axioms fusedMap051swap_checked
#print axioms certified051swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
