/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core097 : Family 7 := level7.get ⟨112,by decide⟩
def sourceMap097 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,7,8,9,10,5,6] (sourceLabel 7 0 1 v)
def fusedMap097 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap097_checked : acceptsGraphIso
    (source (graph core097) (root 7) 0 1) SmallGeFourSpectrum090.graph
      sourceMap097=true := by decide +kernel
theorem fusedMap097_checked : acceptsGraphIso
    (fused (graph core097) (root 7) 0 1) SmallGeFourSpectrum056.graph
      fusedMap097=true := by decide +kernel
theorem certified097 : Certified (graph core097) (root 7) 0 1 :=
  of_native_maps core097 SmallGeFourSpectrum090.graph SmallGeFourSpectrum056.graph
    sourceMap097 fusedMap097 sourceMap097_checked fusedMap097_checked
    SmallGeFourComparisons.comparison097
#print axioms sourceMap097_checked
#print axioms fusedMap097_checked
#print axioms certified097
def sourceMap097swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,7,8,9,5,6,10] (sourceLabel 7 1 0 v)
def fusedMap097swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap097swap_checked : acceptsGraphIso
    (source (graph core097) (root 7) 1 0) SmallGeFourSpectrum090.graph
      sourceMap097swap=true := by decide +kernel
theorem fusedMap097swap_checked : acceptsGraphIso
    (fused (graph core097) (root 7) 1 0) SmallGeFourSpectrum056.graph
      fusedMap097swap=true := by decide +kernel
theorem certified097swap : Certified (graph core097) (root 7) 1 0 :=
  of_native_maps core097 SmallGeFourSpectrum090.graph SmallGeFourSpectrum056.graph
    sourceMap097swap fusedMap097swap sourceMap097swap_checked fusedMap097swap_checked
    SmallGeFourComparisons.comparison097
#print axioms sourceMap097swap_checked
#print axioms fusedMap097swap_checked
#print axioms certified097swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
