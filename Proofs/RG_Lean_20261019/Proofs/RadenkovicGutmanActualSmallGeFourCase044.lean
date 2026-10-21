/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core044 : Family 6 := level6.get ⟨45,by decide⟩
def sourceMap044 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 0 2 v)
def fusedMap044 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap044_checked : acceptsGraphIso
    (source (graph core044) (root 6) 0 2) SmallGeFourSpectrum056.graph
      sourceMap044=true := by decide +kernel
theorem fusedMap044_checked : acceptsGraphIso
    (fused (graph core044) (root 6) 0 2) SmallGeFourSpectrum058.graph
      fusedMap044=true := by decide +kernel
theorem certified044 : Certified (graph core044) (root 6) 0 2 :=
  of_native_maps core044 SmallGeFourSpectrum056.graph SmallGeFourSpectrum058.graph
    sourceMap044 fusedMap044 sourceMap044_checked fusedMap044_checked
    SmallGeFourComparisons.comparison044
#print axioms sourceMap044_checked
#print axioms fusedMap044_checked
#print axioms certified044
def sourceMap044swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,7] (sourceLabel 6 2 0 v)
def fusedMap044swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap044swap_checked : acceptsGraphIso
    (source (graph core044) (root 6) 2 0) SmallGeFourSpectrum056.graph
      sourceMap044swap=true := by decide +kernel
theorem fusedMap044swap_checked : acceptsGraphIso
    (fused (graph core044) (root 6) 2 0) SmallGeFourSpectrum058.graph
      fusedMap044swap=true := by decide +kernel
theorem certified044swap : Certified (graph core044) (root 6) 2 0 :=
  of_native_maps core044 SmallGeFourSpectrum056.graph SmallGeFourSpectrum058.graph
    sourceMap044swap fusedMap044swap sourceMap044swap_checked fusedMap044swap_checked
    SmallGeFourComparisons.comparison044
#print axioms sourceMap044swap_checked
#print axioms fusedMap044swap_checked
#print axioms certified044swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
