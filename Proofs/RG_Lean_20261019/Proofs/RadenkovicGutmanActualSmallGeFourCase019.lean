/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core019 : Family 5 := level5.get ⟨18,by decide⟩
def sourceMap019 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,6,7,8,4,5,0,9,10,11] (sourceLabel 5 1 3 v)
def fusedMap019 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 1 3 v)
theorem sourceMap019_checked : acceptsGraphIso
    (source (graph core019) (root 5) 1 3) SmallGeFourSpectrum169.graph
      sourceMap019=true := by decide +kernel
theorem fusedMap019_checked : acceptsGraphIso
    (fused (graph core019) (root 5) 1 3) SmallGeFourSpectrum104.graph
      fusedMap019=true := by decide +kernel
theorem certified019 : Certified (graph core019) (root 5) 1 3 :=
  of_native_maps core019 SmallGeFourSpectrum169.graph SmallGeFourSpectrum104.graph
    sourceMap019 fusedMap019 sourceMap019_checked fusedMap019_checked
    SmallGeFourComparisons.comparison019
#print axioms sourceMap019_checked
#print axioms fusedMap019_checked
#print axioms certified019
def sourceMap019swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,2,3,6,7,8,0,9,10,11,4,5] (sourceLabel 5 3 1 v)
def fusedMap019swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 3 1 v)
theorem sourceMap019swap_checked : acceptsGraphIso
    (source (graph core019) (root 5) 3 1) SmallGeFourSpectrum169.graph
      sourceMap019swap=true := by decide +kernel
theorem fusedMap019swap_checked : acceptsGraphIso
    (fused (graph core019) (root 5) 3 1) SmallGeFourSpectrum104.graph
      fusedMap019swap=true := by decide +kernel
theorem certified019swap : Certified (graph core019) (root 5) 3 1 :=
  of_native_maps core019 SmallGeFourSpectrum169.graph SmallGeFourSpectrum104.graph
    sourceMap019swap fusedMap019swap sourceMap019swap_checked fusedMap019swap_checked
    SmallGeFourComparisons.comparison019
#print axioms sourceMap019swap_checked
#print axioms fusedMap019swap_checked
#print axioms certified019swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
