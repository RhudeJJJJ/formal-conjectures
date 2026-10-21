/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core037 : Family 6 := level6.get ⟨43,by decide⟩
def sourceMap037 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,6,7,8,9,4,5] (sourceLabel 6 0 1 v)
def fusedMap037 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap037_checked : acceptsGraphIso
    (source (graph core037) (root 6) 0 1) SmallGeFourSpectrum032.graph
      sourceMap037=true := by decide +kernel
theorem fusedMap037_checked : acceptsGraphIso
    (fused (graph core037) (root 6) 0 1) SmallGeFourSpectrum017.graph
      fusedMap037=true := by decide +kernel
theorem certified037 : Certified (graph core037) (root 6) 0 1 :=
  of_native_maps core037 SmallGeFourSpectrum032.graph SmallGeFourSpectrum017.graph
    sourceMap037 fusedMap037 sourceMap037_checked fusedMap037_checked
    SmallGeFourComparisons.comparison037
#print axioms sourceMap037_checked
#print axioms fusedMap037_checked
#print axioms certified037
def sourceMap037swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,6,7,8,4,5,9] (sourceLabel 6 1 0 v)
def fusedMap037swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap037swap_checked : acceptsGraphIso
    (source (graph core037) (root 6) 1 0) SmallGeFourSpectrum032.graph
      sourceMap037swap=true := by decide +kernel
theorem fusedMap037swap_checked : acceptsGraphIso
    (fused (graph core037) (root 6) 1 0) SmallGeFourSpectrum017.graph
      fusedMap037swap=true := by decide +kernel
theorem certified037swap : Certified (graph core037) (root 6) 1 0 :=
  of_native_maps core037 SmallGeFourSpectrum032.graph SmallGeFourSpectrum017.graph
    sourceMap037swap fusedMap037swap sourceMap037swap_checked fusedMap037swap_checked
    SmallGeFourComparisons.comparison037
#print axioms sourceMap037swap_checked
#print axioms fusedMap037swap_checked
#print axioms certified037swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
