/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core073 : Family 7 := level7.get ⟨98,by decide⟩
def sourceMap073 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,8,9,10,1,2,5,6,7,3,4] (sourceLabel 7 0 1 v)
def fusedMap073 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,7,8,9,10,4,5,6] (fusedLabel 7 0 1 v)
theorem sourceMap073_checked : acceptsGraphIso
    (source (graph core073) (root 7) 0 1) SmallGeFourSpectrum056.graph
      sourceMap073=true := by decide +kernel
theorem fusedMap073_checked : acceptsGraphIso
    (fused (graph core073) (root 7) 0 1) SmallGeFourSpectrum067.graph
      fusedMap073=true := by decide +kernel
theorem certified073 : Certified (graph core073) (root 7) 0 1 :=
  of_native_maps core073 SmallGeFourSpectrum056.graph SmallGeFourSpectrum067.graph
    sourceMap073 fusedMap073 sourceMap073_checked fusedMap073_checked
    SmallGeFourComparisons.comparison073
#print axioms sourceMap073_checked
#print axioms fusedMap073_checked
#print axioms certified073
def sourceMap073swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,8,9,10,1,2,5,6,3,4,7] (sourceLabel 7 1 0 v)
def fusedMap073swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,7,8,9,10,4,5,6] (fusedLabel 7 1 0 v)
theorem sourceMap073swap_checked : acceptsGraphIso
    (source (graph core073) (root 7) 1 0) SmallGeFourSpectrum056.graph
      sourceMap073swap=true := by decide +kernel
theorem fusedMap073swap_checked : acceptsGraphIso
    (fused (graph core073) (root 7) 1 0) SmallGeFourSpectrum067.graph
      fusedMap073swap=true := by decide +kernel
theorem certified073swap : Certified (graph core073) (root 7) 1 0 :=
  of_native_maps core073 SmallGeFourSpectrum056.graph SmallGeFourSpectrum067.graph
    sourceMap073swap fusedMap073swap sourceMap073swap_checked fusedMap073swap_checked
    SmallGeFourComparisons.comparison073
#print axioms sourceMap073swap_checked
#print axioms fusedMap073swap_checked
#print axioms certified073swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
