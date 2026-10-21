/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core068 : Family 7 := level7.get ⟨93,by decide⟩
def sourceMap068 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,7,8,9,2,3,4,5,6] (sourceLabel 7 0 0 v)
def fusedMap068 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,6,7,8,9,3,4,5,1,2] (fusedLabel 7 0 0 v)
theorem sourceMap068_checked : acceptsGraphIso
    (source (graph core068) (root 7) 0 0) SmallGeFourSpectrum029.graph
      sourceMap068=true := by decide +kernel
theorem fusedMap068_checked : acceptsGraphIso
    (fused (graph core068) (root 7) 0 0) SmallGeFourSpectrum021.graph
      fusedMap068=true := by decide +kernel
theorem certified068 : Certified (graph core068) (root 7) 0 0 :=
  of_native_maps core068 SmallGeFourSpectrum029.graph SmallGeFourSpectrum021.graph
    sourceMap068 fusedMap068 sourceMap068_checked fusedMap068_checked
    SmallGeFourComparisons.comparison068
#print axioms sourceMap068_checked
#print axioms fusedMap068_checked
#print axioms certified068
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
