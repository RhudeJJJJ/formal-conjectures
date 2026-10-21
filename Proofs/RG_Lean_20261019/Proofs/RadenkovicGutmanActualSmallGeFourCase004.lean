/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core004 : Family 4 := level4.get ⟨8,by decide⟩
def sourceMap004 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 5) → Fin 11 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10] (sourceLabel 4 0 4 v)
def fusedMap004 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 0 4 v)
theorem sourceMap004_checked : acceptsGraphIso
    (source (graph core004) (root 4) 0 4) SmallGeFourSpectrum044.graph
      sourceMap004=true := by decide +kernel
theorem fusedMap004_checked : acceptsGraphIso
    (fused (graph core004) (root 4) 0 4) SmallGeFourSpectrum037.graph
      fusedMap004=true := by decide +kernel
theorem certified004 : Certified (graph core004) (root 4) 0 4 :=
  of_native_maps core004 SmallGeFourSpectrum044.graph SmallGeFourSpectrum037.graph
    sourceMap004 fusedMap004 sourceMap004_checked fusedMap004_checked
    SmallGeFourComparisons.comparison004
#print axioms sourceMap004_checked
#print axioms fusedMap004_checked
#print axioms certified004
def sourceMap004swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,8,9,10,7] (sourceLabel 4 4 0 v)
def fusedMap004swap : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 4 0 v)
theorem sourceMap004swap_checked : acceptsGraphIso
    (source (graph core004) (root 4) 4 0) SmallGeFourSpectrum044.graph
      sourceMap004swap=true := by decide +kernel
theorem fusedMap004swap_checked : acceptsGraphIso
    (fused (graph core004) (root 4) 4 0) SmallGeFourSpectrum037.graph
      fusedMap004swap=true := by decide +kernel
theorem certified004swap : Certified (graph core004) (root 4) 4 0 :=
  of_native_maps core004 SmallGeFourSpectrum044.graph SmallGeFourSpectrum037.graph
    sourceMap004swap fusedMap004swap sourceMap004swap_checked fusedMap004swap_checked
    SmallGeFourComparisons.comparison004
#print axioms sourceMap004swap_checked
#print axioms fusedMap004swap_checked
#print axioms certified004swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
