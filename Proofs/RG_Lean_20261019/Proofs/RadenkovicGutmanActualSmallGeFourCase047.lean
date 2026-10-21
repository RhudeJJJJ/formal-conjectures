/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core047 : Family 6 := level6.get ⟨45,by decide⟩
def sourceMap047 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,7,8,5,6,9,10,11] (sourceLabel 6 1 2 v)
def fusedMap047 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap047_checked : acceptsGraphIso
    (source (graph core047) (root 6) 1 2) SmallGeFourSpectrum164.graph
      sourceMap047=true := by decide +kernel
theorem fusedMap047_checked : acceptsGraphIso
    (fused (graph core047) (root 6) 1 2) SmallGeFourSpectrum099.graph
      fusedMap047=true := by decide +kernel
theorem certified047 : Certified (graph core047) (root 6) 1 2 :=
  of_native_maps core047 SmallGeFourSpectrum164.graph SmallGeFourSpectrum099.graph
    sourceMap047 fusedMap047 sourceMap047_checked fusedMap047_checked
    SmallGeFourComparisons.comparison047
#print axioms sourceMap047_checked
#print axioms fusedMap047_checked
#print axioms certified047
def sourceMap047swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,7,8,9,10,11,5,6] (sourceLabel 6 2 1 v)
def fusedMap047swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap047swap_checked : acceptsGraphIso
    (source (graph core047) (root 6) 2 1) SmallGeFourSpectrum164.graph
      sourceMap047swap=true := by decide +kernel
theorem fusedMap047swap_checked : acceptsGraphIso
    (fused (graph core047) (root 6) 2 1) SmallGeFourSpectrum099.graph
      fusedMap047swap=true := by decide +kernel
theorem certified047swap : Certified (graph core047) (root 6) 2 1 :=
  of_native_maps core047 SmallGeFourSpectrum164.graph SmallGeFourSpectrum099.graph
    sourceMap047swap fusedMap047swap sourceMap047swap_checked fusedMap047swap_checked
    SmallGeFourComparisons.comparison047
#print axioms sourceMap047swap_checked
#print axioms fusedMap047swap_checked
#print axioms certified047swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
