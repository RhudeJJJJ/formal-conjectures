/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core059 : Family 6 := level6.get ⟨47,by decide⟩
def sourceMap059 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,3,4,5,6,7,8,1,2,9,10,11] (sourceLabel 6 1 2 v)
def fusedMap059 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap059_checked : acceptsGraphIso
    (source (graph core059) (root 6) 1 2) SmallGeFourSpectrum178.graph
      sourceMap059=true := by decide +kernel
theorem fusedMap059_checked : acceptsGraphIso
    (fused (graph core059) (root 6) 1 2) SmallGeFourSpectrum116.graph
      fusedMap059=true := by decide +kernel
theorem certified059 : Certified (graph core059) (root 6) 1 2 :=
  of_native_maps core059 SmallGeFourSpectrum178.graph SmallGeFourSpectrum116.graph
    sourceMap059 fusedMap059 sourceMap059_checked fusedMap059_checked
    SmallGeFourComparisons.comparison059
#print axioms sourceMap059_checked
#print axioms fusedMap059_checked
#print axioms certified059
def sourceMap059swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,3,4,5,6,7,8,9,10,11,1,2] (sourceLabel 6 2 1 v)
def fusedMap059swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap059swap_checked : acceptsGraphIso
    (source (graph core059) (root 6) 2 1) SmallGeFourSpectrum178.graph
      sourceMap059swap=true := by decide +kernel
theorem fusedMap059swap_checked : acceptsGraphIso
    (fused (graph core059) (root 6) 2 1) SmallGeFourSpectrum116.graph
      fusedMap059swap=true := by decide +kernel
theorem certified059swap : Certified (graph core059) (root 6) 2 1 :=
  of_native_maps core059 SmallGeFourSpectrum178.graph SmallGeFourSpectrum116.graph
    sourceMap059swap fusedMap059swap sourceMap059swap_checked fusedMap059swap_checked
    SmallGeFourComparisons.comparison059
#print axioms sourceMap059swap_checked
#print axioms fusedMap059swap_checked
#print axioms certified059swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
