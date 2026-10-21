/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core041 : Family 6 := level6.get ⟨43,by decide⟩
def sourceMap041 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,6,7,8,4,5,9,10,11] (sourceLabel 6 1 2 v)
def fusedMap041 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap041_checked : acceptsGraphIso
    (source (graph core041) (root 6) 1 2) SmallGeFourSpectrum141.graph
      sourceMap041=true := by decide +kernel
theorem fusedMap041_checked : acceptsGraphIso
    (fused (graph core041) (root 6) 1 2) SmallGeFourSpectrum095.graph
      fusedMap041=true := by decide +kernel
theorem certified041 : Certified (graph core041) (root 6) 1 2 :=
  of_native_maps core041 SmallGeFourSpectrum141.graph SmallGeFourSpectrum095.graph
    sourceMap041 fusedMap041 sourceMap041_checked fusedMap041_checked
    SmallGeFourComparisons.comparison041
#print axioms sourceMap041_checked
#print axioms fusedMap041_checked
#print axioms certified041
def sourceMap041swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,6,7,8,9,10,11,4,5] (sourceLabel 6 2 1 v)
def fusedMap041swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap041swap_checked : acceptsGraphIso
    (source (graph core041) (root 6) 2 1) SmallGeFourSpectrum141.graph
      sourceMap041swap=true := by decide +kernel
theorem fusedMap041swap_checked : acceptsGraphIso
    (fused (graph core041) (root 6) 2 1) SmallGeFourSpectrum095.graph
      fusedMap041swap=true := by decide +kernel
theorem certified041swap : Certified (graph core041) (root 6) 2 1 :=
  of_native_maps core041 SmallGeFourSpectrum141.graph SmallGeFourSpectrum095.graph
    sourceMap041swap fusedMap041swap sourceMap041swap_checked fusedMap041swap_checked
    SmallGeFourComparisons.comparison041
#print axioms sourceMap041swap_checked
#print axioms fusedMap041swap_checked
#print axioms certified041swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
