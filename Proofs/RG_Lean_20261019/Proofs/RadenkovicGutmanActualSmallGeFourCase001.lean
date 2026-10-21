/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core001 : Family 4 := level4.get ⟨8,by decide⟩
def sourceMap001 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (sourceLabel 4 0 1 v)
def fusedMap001 : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![1,2,3,4,5,0,6,7] (fusedLabel 4 0 1 v)
theorem sourceMap001_checked : acceptsGraphIso
    (source (graph core001) (root 4) 0 1) SmallGeFourSpectrum002.graph
      sourceMap001=true := by decide +kernel
theorem fusedMap001_checked : acceptsGraphIso
    (fused (graph core001) (root 4) 0 1) SmallGeFourSpectrum003.graph
      fusedMap001=true := by decide +kernel
theorem certified001 : Certified (graph core001) (root 4) 0 1 :=
  of_native_maps core001 SmallGeFourSpectrum002.graph SmallGeFourSpectrum003.graph
    sourceMap001 fusedMap001 sourceMap001_checked fusedMap001_checked
    SmallGeFourComparisons.comparison001
#print axioms sourceMap001_checked
#print axioms fusedMap001_checked
#print axioms certified001
def sourceMap001swap : (Vertices 4 ⊕ Fin 2 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,1,2,3,4,6,7,5] (sourceLabel 4 1 0 v)
def fusedMap001swap : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![1,2,3,4,5,0,6,7] (fusedLabel 4 1 0 v)
theorem sourceMap001swap_checked : acceptsGraphIso
    (source (graph core001) (root 4) 1 0) SmallGeFourSpectrum002.graph
      sourceMap001swap=true := by decide +kernel
theorem fusedMap001swap_checked : acceptsGraphIso
    (fused (graph core001) (root 4) 1 0) SmallGeFourSpectrum003.graph
      fusedMap001swap=true := by decide +kernel
theorem certified001swap : Certified (graph core001) (root 4) 1 0 :=
  of_native_maps core001 SmallGeFourSpectrum002.graph SmallGeFourSpectrum003.graph
    sourceMap001swap fusedMap001swap sourceMap001swap_checked fusedMap001swap_checked
    SmallGeFourComparisons.comparison001
#print axioms sourceMap001swap_checked
#print axioms fusedMap001swap_checked
#print axioms certified001swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
