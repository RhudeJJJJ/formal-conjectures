/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core090 : Family 7 := level7.get ⟨110,by decide⟩
def sourceMap090 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 0 2 v)
def fusedMap090 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap090_checked : acceptsGraphIso
    (source (graph core090) (root 7) 0 2) SmallGeFourSpectrum146.graph
      sourceMap090=true := by decide +kernel
theorem fusedMap090_checked : acceptsGraphIso
    (fused (graph core090) (root 7) 0 2) SmallGeFourSpectrum149.graph
      fusedMap090=true := by decide +kernel
theorem certified090 : Certified (graph core090) (root 7) 0 2 :=
  of_native_maps core090 SmallGeFourSpectrum146.graph SmallGeFourSpectrum149.graph
    sourceMap090 fusedMap090 sourceMap090_checked fusedMap090_checked
    SmallGeFourComparisons.comparison090
#print axioms sourceMap090_checked
#print axioms fusedMap090_checked
#print axioms certified090
def sourceMap090swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,8] (sourceLabel 7 2 0 v)
def fusedMap090swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap090swap_checked : acceptsGraphIso
    (source (graph core090) (root 7) 2 0) SmallGeFourSpectrum146.graph
      sourceMap090swap=true := by decide +kernel
theorem fusedMap090swap_checked : acceptsGraphIso
    (fused (graph core090) (root 7) 2 0) SmallGeFourSpectrum149.graph
      fusedMap090swap=true := by decide +kernel
theorem certified090swap : Certified (graph core090) (root 7) 2 0 :=
  of_native_maps core090 SmallGeFourSpectrum146.graph SmallGeFourSpectrum149.graph
    sourceMap090swap fusedMap090swap sourceMap090swap_checked fusedMap090swap_checked
    SmallGeFourComparisons.comparison090
#print axioms sourceMap090swap_checked
#print axioms fusedMap090swap_checked
#print axioms certified090swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
