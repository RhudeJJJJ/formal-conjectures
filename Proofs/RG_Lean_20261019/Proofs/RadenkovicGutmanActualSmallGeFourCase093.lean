/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core093 : Family 7 := level7.get ⟨111,by decide⟩
def sourceMap093 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,9,10,7,8] (sourceLabel 7 0 1 v)
def fusedMap093 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap093_checked : acceptsGraphIso
    (source (graph core093) (root 7) 0 1) SmallGeFourSpectrum089.graph
      sourceMap093=true := by decide +kernel
theorem fusedMap093_checked : acceptsGraphIso
    (fused (graph core093) (root 7) 0 1) SmallGeFourSpectrum055.graph
      fusedMap093=true := by decide +kernel
theorem certified093 : Certified (graph core093) (root 7) 0 1 :=
  of_native_maps core093 SmallGeFourSpectrum089.graph SmallGeFourSpectrum055.graph
    sourceMap093 fusedMap093 sourceMap093_checked fusedMap093_checked
    SmallGeFourComparisons.comparison093
#print axioms sourceMap093_checked
#print axioms fusedMap093_checked
#print axioms certified093
def sourceMap093swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8,10] (sourceLabel 7 1 0 v)
def fusedMap093swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap093swap_checked : acceptsGraphIso
    (source (graph core093) (root 7) 1 0) SmallGeFourSpectrum089.graph
      sourceMap093swap=true := by decide +kernel
theorem fusedMap093swap_checked : acceptsGraphIso
    (fused (graph core093) (root 7) 1 0) SmallGeFourSpectrum055.graph
      fusedMap093swap=true := by decide +kernel
theorem certified093swap : Certified (graph core093) (root 7) 1 0 :=
  of_native_maps core093 SmallGeFourSpectrum089.graph SmallGeFourSpectrum055.graph
    sourceMap093swap fusedMap093swap sourceMap093swap_checked fusedMap093swap_checked
    SmallGeFourComparisons.comparison093
#print axioms sourceMap093swap_checked
#print axioms fusedMap093swap_checked
#print axioms certified093swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
