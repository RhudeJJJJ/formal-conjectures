/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core074 : Family 7 := level7.get ⟨98,by decide⟩
def sourceMap074 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,7,8,9,10,11,4,5,6] (sourceLabel 7 0 2 v)
def fusedMap074 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap074_checked : acceptsGraphIso
    (source (graph core074) (root 7) 0 2) SmallGeFourSpectrum195.graph
      sourceMap074=true := by decide +kernel
theorem fusedMap074_checked : acceptsGraphIso
    (fused (graph core074) (root 7) 0 2) SmallGeFourSpectrum107.graph
      fusedMap074=true := by decide +kernel
theorem certified074 : Certified (graph core074) (root 7) 0 2 :=
  of_native_maps core074 SmallGeFourSpectrum195.graph SmallGeFourSpectrum107.graph
    sourceMap074 fusedMap074 sourceMap074_checked fusedMap074_checked
    SmallGeFourComparisons.comparison074
#print axioms sourceMap074_checked
#print axioms fusedMap074_checked
#print axioms certified074
def sourceMap074swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,7,8,9,10,4,5,6,11] (sourceLabel 7 2 0 v)
def fusedMap074swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap074swap_checked : acceptsGraphIso
    (source (graph core074) (root 7) 2 0) SmallGeFourSpectrum195.graph
      sourceMap074swap=true := by decide +kernel
theorem fusedMap074swap_checked : acceptsGraphIso
    (fused (graph core074) (root 7) 2 0) SmallGeFourSpectrum107.graph
      fusedMap074swap=true := by decide +kernel
theorem certified074swap : Certified (graph core074) (root 7) 2 0 :=
  of_native_maps core074 SmallGeFourSpectrum195.graph SmallGeFourSpectrum107.graph
    sourceMap074swap fusedMap074swap sourceMap074swap_checked fusedMap074swap_checked
    SmallGeFourComparisons.comparison074
#print axioms sourceMap074swap_checked
#print axioms fusedMap074swap_checked
#print axioms certified074swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
