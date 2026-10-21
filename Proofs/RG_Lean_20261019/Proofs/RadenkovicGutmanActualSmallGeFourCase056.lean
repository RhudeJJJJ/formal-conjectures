/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core056 : Family 6 := level6.get ⟨47,by decide⟩
def sourceMap056 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10] (sourceLabel 6 0 2 v)
def fusedMap056 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap056_checked : acceptsGraphIso
    (source (graph core056) (root 6) 0 2) SmallGeFourSpectrum071.graph
      sourceMap056=true := by decide +kernel
theorem fusedMap056_checked : acceptsGraphIso
    (fused (graph core056) (root 6) 0 2) SmallGeFourSpectrum040.graph
      fusedMap056=true := by decide +kernel
theorem certified056 : Certified (graph core056) (root 6) 0 2 :=
  of_native_maps core056 SmallGeFourSpectrum071.graph SmallGeFourSpectrum040.graph
    sourceMap056 fusedMap056 sourceMap056_checked fusedMap056_checked
    SmallGeFourComparisons.comparison056
#print axioms sourceMap056_checked
#print axioms fusedMap056_checked
#print axioms certified056
def sourceMap056swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,8] (sourceLabel 6 2 0 v)
def fusedMap056swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap056swap_checked : acceptsGraphIso
    (source (graph core056) (root 6) 2 0) SmallGeFourSpectrum071.graph
      sourceMap056swap=true := by decide +kernel
theorem fusedMap056swap_checked : acceptsGraphIso
    (fused (graph core056) (root 6) 2 0) SmallGeFourSpectrum040.graph
      fusedMap056swap=true := by decide +kernel
theorem certified056swap : Certified (graph core056) (root 6) 2 0 :=
  of_native_maps core056 SmallGeFourSpectrum071.graph SmallGeFourSpectrum040.graph
    sourceMap056swap fusedMap056swap sourceMap056swap_checked fusedMap056swap_checked
    SmallGeFourComparisons.comparison056
#print axioms sourceMap056swap_checked
#print axioms fusedMap056swap_checked
#print axioms certified056swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
