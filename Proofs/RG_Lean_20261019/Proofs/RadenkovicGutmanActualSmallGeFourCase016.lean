/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core016 : Family 5 := level5.get ⟨18,by decide⟩
def sourceMap016 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap016 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap016_checked : acceptsGraphIso
    (source (graph core016) (root 5) 0 4) SmallGeFourSpectrum100.graph
      sourceMap016=true := by decide +kernel
theorem fusedMap016_checked : acceptsGraphIso
    (fused (graph core016) (root 5) 0 4) SmallGeFourSpectrum104.graph
      fusedMap016=true := by decide +kernel
theorem certified016 : Certified (graph core016) (root 5) 0 4 :=
  of_native_maps core016 SmallGeFourSpectrum100.graph SmallGeFourSpectrum104.graph
    sourceMap016 fusedMap016 sourceMap016_checked fusedMap016_checked
    SmallGeFourComparisons.comparison016
#print axioms sourceMap016_checked
#print axioms fusedMap016_checked
#print axioms certified016
def sourceMap016swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,7] (sourceLabel 5 4 0 v)
def fusedMap016swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap016swap_checked : acceptsGraphIso
    (source (graph core016) (root 5) 4 0) SmallGeFourSpectrum100.graph
      sourceMap016swap=true := by decide +kernel
theorem fusedMap016swap_checked : acceptsGraphIso
    (fused (graph core016) (root 5) 4 0) SmallGeFourSpectrum104.graph
      fusedMap016swap=true := by decide +kernel
theorem certified016swap : Certified (graph core016) (root 5) 4 0 :=
  of_native_maps core016 SmallGeFourSpectrum100.graph SmallGeFourSpectrum104.graph
    sourceMap016swap fusedMap016swap sourceMap016swap_checked fusedMap016swap_checked
    SmallGeFourComparisons.comparison016
#print axioms sourceMap016swap_checked
#print axioms fusedMap016swap_checked
#print axioms certified016swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
