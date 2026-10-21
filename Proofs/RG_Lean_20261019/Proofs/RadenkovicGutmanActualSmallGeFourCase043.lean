/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core043 : Family 6 := level6.get ⟨45,by decide⟩
def sourceMap043 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,7,8,9,5,6] (sourceLabel 6 0 1 v)
def fusedMap043 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap043_checked : acceptsGraphIso
    (source (graph core043) (root 6) 0 1) SmallGeFourSpectrum034.graph
      sourceMap043=true := by decide +kernel
theorem fusedMap043_checked : acceptsGraphIso
    (fused (graph core043) (root 6) 0 1) SmallGeFourSpectrum019.graph
      fusedMap043=true := by decide +kernel
theorem certified043 : Certified (graph core043) (root 6) 0 1 :=
  of_native_maps core043 SmallGeFourSpectrum034.graph SmallGeFourSpectrum019.graph
    sourceMap043 fusedMap043 sourceMap043_checked fusedMap043_checked
    SmallGeFourComparisons.comparison043
#print axioms sourceMap043_checked
#print axioms fusedMap043_checked
#print axioms certified043
def sourceMap043swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,7,8,5,6,9] (sourceLabel 6 1 0 v)
def fusedMap043swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap043swap_checked : acceptsGraphIso
    (source (graph core043) (root 6) 1 0) SmallGeFourSpectrum034.graph
      sourceMap043swap=true := by decide +kernel
theorem fusedMap043swap_checked : acceptsGraphIso
    (fused (graph core043) (root 6) 1 0) SmallGeFourSpectrum019.graph
      fusedMap043swap=true := by decide +kernel
theorem certified043swap : Certified (graph core043) (root 6) 1 0 :=
  of_native_maps core043 SmallGeFourSpectrum034.graph SmallGeFourSpectrum019.graph
    sourceMap043swap fusedMap043swap sourceMap043swap_checked fusedMap043swap_checked
    SmallGeFourComparisons.comparison043
#print axioms sourceMap043swap_checked
#print axioms fusedMap043swap_checked
#print axioms certified043swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
