/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core057 : Family 6 := level6.get ⟨47,by decide⟩
def sourceMap057 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (sourceLabel 6 0 3 v)
def fusedMap057 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap057_checked : acceptsGraphIso
    (source (graph core057) (root 6) 0 3) SmallGeFourSpectrum112.graph
      sourceMap057=true := by decide +kernel
theorem fusedMap057_checked : acceptsGraphIso
    (fused (graph core057) (root 6) 0 3) SmallGeFourSpectrum116.graph
      fusedMap057=true := by decide +kernel
theorem certified057 : Certified (graph core057) (root 6) 0 3 :=
  of_native_maps core057 SmallGeFourSpectrum112.graph SmallGeFourSpectrum116.graph
    sourceMap057 fusedMap057 sourceMap057_checked fusedMap057_checked
    SmallGeFourComparisons.comparison057
#print axioms sourceMap057_checked
#print axioms fusedMap057_checked
#print axioms certified057
def sourceMap057swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,8] (sourceLabel 6 3 0 v)
def fusedMap057swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap057swap_checked : acceptsGraphIso
    (source (graph core057) (root 6) 3 0) SmallGeFourSpectrum112.graph
      sourceMap057swap=true := by decide +kernel
theorem fusedMap057swap_checked : acceptsGraphIso
    (fused (graph core057) (root 6) 3 0) SmallGeFourSpectrum116.graph
      fusedMap057swap=true := by decide +kernel
theorem certified057swap : Certified (graph core057) (root 6) 3 0 :=
  of_native_maps core057 SmallGeFourSpectrum112.graph SmallGeFourSpectrum116.graph
    sourceMap057swap fusedMap057swap sourceMap057swap_checked fusedMap057swap_checked
    SmallGeFourComparisons.comparison057
#print axioms sourceMap057swap_checked
#print axioms fusedMap057swap_checked
#print axioms certified057swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
