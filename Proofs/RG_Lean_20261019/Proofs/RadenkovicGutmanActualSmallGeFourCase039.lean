/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core039 : Family 6 := level6.get ⟨43,by decide⟩
def sourceMap039 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (sourceLabel 6 0 3 v)
def fusedMap039 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap039_checked : acceptsGraphIso
    (source (graph core039) (root 6) 0 3) SmallGeFourSpectrum149.graph
      sourceMap039=true := by decide +kernel
theorem fusedMap039_checked : acceptsGraphIso
    (fused (graph core039) (root 6) 0 3) SmallGeFourSpectrum095.graph
      fusedMap039=true := by decide +kernel
theorem certified039 : Certified (graph core039) (root 6) 0 3 :=
  of_native_maps core039 SmallGeFourSpectrum149.graph SmallGeFourSpectrum095.graph
    sourceMap039 fusedMap039 sourceMap039_checked fusedMap039_checked
    SmallGeFourComparisons.comparison039
#print axioms sourceMap039_checked
#print axioms fusedMap039_checked
#print axioms certified039
def sourceMap039swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,8] (sourceLabel 6 3 0 v)
def fusedMap039swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap039swap_checked : acceptsGraphIso
    (source (graph core039) (root 6) 3 0) SmallGeFourSpectrum149.graph
      sourceMap039swap=true := by decide +kernel
theorem fusedMap039swap_checked : acceptsGraphIso
    (fused (graph core039) (root 6) 3 0) SmallGeFourSpectrum095.graph
      fusedMap039swap=true := by decide +kernel
theorem certified039swap : Certified (graph core039) (root 6) 3 0 :=
  of_native_maps core039 SmallGeFourSpectrum149.graph SmallGeFourSpectrum095.graph
    sourceMap039swap fusedMap039swap sourceMap039swap_checked fusedMap039swap_checked
    SmallGeFourComparisons.comparison039
#print axioms sourceMap039swap_checked
#print axioms fusedMap039swap_checked
#print axioms certified039swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
