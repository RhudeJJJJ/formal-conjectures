/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core002 : Family 4 := level4.get ⟨8,by decide⟩
def sourceMap002 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 3) → Fin 9 :=
  fun v => ![1,2,3,4,5,6,0,7,8] (sourceLabel 4 0 2 v)
def fusedMap002 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (fusedLabel 4 0 2 v)
theorem sourceMap002_checked : acceptsGraphIso
    (source (graph core002) (root 4) 0 2) SmallGeFourSpectrum010.graph
      sourceMap002=true := by decide +kernel
theorem fusedMap002_checked : acceptsGraphIso
    (fused (graph core002) (root 4) 0 2) SmallGeFourSpectrum006.graph
      fusedMap002=true := by decide +kernel
theorem certified002 : Certified (graph core002) (root 4) 0 2 :=
  of_native_maps core002 SmallGeFourSpectrum010.graph SmallGeFourSpectrum006.graph
    sourceMap002 fusedMap002 sourceMap002_checked fusedMap002_checked
    SmallGeFourComparisons.comparison002
#print axioms sourceMap002_checked
#print axioms fusedMap002_checked
#print axioms certified002
def sourceMap002swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,7,8,6] (sourceLabel 4 2 0 v)
def fusedMap002swap : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (fusedLabel 4 2 0 v)
theorem sourceMap002swap_checked : acceptsGraphIso
    (source (graph core002) (root 4) 2 0) SmallGeFourSpectrum010.graph
      sourceMap002swap=true := by decide +kernel
theorem fusedMap002swap_checked : acceptsGraphIso
    (fused (graph core002) (root 4) 2 0) SmallGeFourSpectrum006.graph
      fusedMap002swap=true := by decide +kernel
theorem certified002swap : Certified (graph core002) (root 4) 2 0 :=
  of_native_maps core002 SmallGeFourSpectrum010.graph SmallGeFourSpectrum006.graph
    sourceMap002swap fusedMap002swap sourceMap002swap_checked fusedMap002swap_checked
    SmallGeFourComparisons.comparison002
#print axioms sourceMap002swap_checked
#print axioms fusedMap002swap_checked
#print axioms certified002swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
