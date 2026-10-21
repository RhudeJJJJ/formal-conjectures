/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core049 : Family 6 := level6.get ⟨46,by decide⟩
def sourceMap049 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,5,6,7,8,9,3,4] (sourceLabel 6 0 1 v)
def fusedMap049 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap049_checked : acceptsGraphIso
    (source (graph core049) (root 6) 0 1) SmallGeFourSpectrum035.graph
      sourceMap049=true := by decide +kernel
theorem fusedMap049_checked : acceptsGraphIso
    (fused (graph core049) (root 6) 0 1) SmallGeFourSpectrum020.graph
      fusedMap049=true := by decide +kernel
theorem certified049 : Certified (graph core049) (root 6) 0 1 :=
  of_native_maps core049 SmallGeFourSpectrum035.graph SmallGeFourSpectrum020.graph
    sourceMap049 fusedMap049 sourceMap049_checked fusedMap049_checked
    SmallGeFourComparisons.comparison049
#print axioms sourceMap049_checked
#print axioms fusedMap049_checked
#print axioms certified049
def sourceMap049swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,5,6,7,8,3,4,9] (sourceLabel 6 1 0 v)
def fusedMap049swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap049swap_checked : acceptsGraphIso
    (source (graph core049) (root 6) 1 0) SmallGeFourSpectrum035.graph
      sourceMap049swap=true := by decide +kernel
theorem fusedMap049swap_checked : acceptsGraphIso
    (fused (graph core049) (root 6) 1 0) SmallGeFourSpectrum020.graph
      fusedMap049swap=true := by decide +kernel
theorem certified049swap : Certified (graph core049) (root 6) 1 0 :=
  of_native_maps core049 SmallGeFourSpectrum035.graph SmallGeFourSpectrum020.graph
    sourceMap049swap fusedMap049swap sourceMap049swap_checked fusedMap049swap_checked
    SmallGeFourComparisons.comparison049
#print axioms sourceMap049swap_checked
#print axioms fusedMap049swap_checked
#print axioms certified049swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
